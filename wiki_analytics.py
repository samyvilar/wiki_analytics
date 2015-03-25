#! /usr/bin/env python
__author__ = 'samyvilar'

import os
import argparse
import functools
import itertools
import collections
import xmllib
import httplib
import urlparse
import Queue
import logging
import datetime
import threading
import time
import json
import atexit

import lxml.html as html
import bottle

wiki_scheme = 'http'
wiki_hostname = 'en.wikipedia.org'
wiki_port = 80
wiki_article_path = '/wiki/'

def article_url_tail(url):
    parts = urlparse.urlparse(url)
    if parts.netloc:
        assert parts.netloc == wiki_hostname
    path = parts.path
    if not path.startswith(wiki_article_path):
        raise ValueError('Urls: {} path must start with {} got {}'.format(url, wiki_article_path, path))
    return path[len(wiki_article_path):]

conn_pool_size = 10
conn_pool = Queue.Queue(conn_pool_size)  # To be used when multi-threading supported is added

def get_or_make_conn(timeout=None, make=functools.partial(httplib.HTTPConnection, wiki_hostname, wiki_port)):
    # Get or Make an http connection
    if timeout is not None:  # If default is giving then we cant used conns from pool
        return make(timeout=timeout)
    try:
        return conn_pool.get_nowait()
    except Queue.Empty:
        return make()


def recycle_conn(conn): # To be used when multi-threading support is added
    try:
        conn_pool.put_nowait(conn)
    except Queue.Full:
        pass


def rand_article_path(wiki_special_rand_path=wiki_article_path + 'Special:Random'):
    conn = get_or_make_conn()
    conn.request('HEAD', wiki_special_rand_path)
    resp = conn.getresponse()
    location = resp.getheader('location')
    resp.read()
    recycle_conn(conn)
    url = urlparse.urlparse(location)
    return url.path


def last_modified_on(origin, elem_id='footer-info-lastmod', parsing_format=' This page was last modified on %d %B %Y, at %H:%M.'):
    """ Returns the datetime object representing the last time the article was modified,
            upon failure it tries the header, if that fails, it returns None
    :param origin: parsed html object
    :param elem_id: container id, defaults to 'footer-info-lastmod'
    :param parsing_format: expected format str defaults to: ' This page was last modified on %d %B %Y, at %H:%M.'
    :return: datetime object or None on failure.
    >>> import lxml.html
    >>> obj = last_modified_on(lxml.html.parse('http://en.wikipedia.org/wiki/Computer_science').getroot())
    >>> assert type(obj) is datetime.datetime
    >>> obj = last_modified_on(lxml.html.parse('http://en.wikipedia.org/wiki/States_and_union_territories_of_India').getroot())
    >>> assert obj
    """
    format_error = functools.partial(
        'Failed to get wiki article last modified date time, url: {url}, error: {er}'.format,
         url=origin.base_url
    )
    try:
        return datetime.datetime.strptime(origin.get_element_by_id(elem_id).text, parsing_format)
    except (KeyError, ValueError) as er:
        logging.exception(format_error(er=er))
        raise er
    conn = get_or_make_conn()
    conn.request('HEAD', urlparse.urlparse(origin.base_url).path)
    resp = conn.getresponse()
    last_modified_on = resp.getheader('last-modified') # Try the header
    resp.read()
    recycle_conn(conn)
    if last_modified_on:
        try:
            return datetime.datetime.strptime(last_modified_on, '%a, %d %b %Y %H:%M:%S %Z')
        except ValueError as er:
            logging.exception('Failed to get last-modified header: {}'.format(er))
            raise er
    else:
        logging.warning('Unable to determine wiki article url: {} last modified date time.'.format(origin.base_url))

def iter_text_links_path(origin, elem_id='mw-content-text', from_url=None): # TODO: deal with red links.
    """ Gets all the text links from an html node,
        according to http://en.wikipedia.org/wiki/Wikipedia:Getting_to_Philosophy
            taken only those links that are non-parenthesized, non-italicized
            while Ignoring external links, links to the current page, [or red links Currently not supported!]
    :param origin: root html node.
    :param elem_id: container id to search within, defaults to 'mw-content-text',
        must be updated if/when wikipedia changes their template
    :return: iterator of links to possibly other articles (as they are present in the text)
    >>> import lxml.html
    >>> print next(iter_text_links_path(lxml.html.parse('http://en.wikipedia.org/wiki/Human').getroot()))
    /wiki/Hominini
    >>> print next(iter_text_links_path(lxml.html.parse('http://en.wikipedia.org/wiki/Mississippi').getroot()))
    /wiki/U.S._state
    >>> print next(iter_text_links_path(lxml.html.parse('http://en.wikipedia.org/wiki/Al-Ahram_Center_for_Political_and_Strategic_Studies').getroot()))
    /wiki/Zionism
    """
    current_path = urlparse.urlparse(origin.base_url).path
    for p in origin.get_element_by_id(elem_id).iterfind('p'):
        paren_count = 0
        for node in p.iterchildren():
            # Remove any links found within parenthesis, such as "(from Greek: ..."
            # Assumes that the paren do NOT cross paragraph <p> tags and aren't malformed.
            if paren_count:
                p.remove(node)
            text = node.tail or ''
            for char in text: # <<<< Explore text, count number of open/close parenthesis.
                if char == '(':
                    paren_count += 1
                elif char == ')':
                    paren_count -= 1
        for node in p.iterchildren('a'):
            if node.find('i') is None: # remove any italicized links.
                link = node.get('href', '')
                url = urlparse.urlparse(link)
                netloc = url.netloc or wiki_hostname
                path = url.path or current_path
                if not (netloc != wiki_hostname or path == current_path or 'redlink=1' in url.query):
                    # Ignore External links/self referencing/redlinks Links
                    yield link

Article = collections.namedtuple('Article', ('first_link', 'url_tail', 'modified_on'))

def cached(callable=None, cache=None, key=lambda *args, **kwargs: args and args[0]):
    cache = cache or {}
    def from_cache(*args, **kwargs):
        index = key(*args, **kwargs)
        if isinstance(index, collections.Hashable):  # Try the cache only if index is hashable otherwise bail.
            if index not in cache:
                cache[index] = callable(*args, **kwargs)
            return cache[index]
        return callable(*args, **kwargs)
    return functools.partial(cached, cache=cache, key=key) if callable is None \
        else functools.wraps(callable)(from_cache) # ^^^^ if decorator with args but missing callable.

class NotFoundException(httplib.HTTPException):
    pass

# @cached
def article(source=None, wiki_site='{scheme}://{host}'.format(scheme=wiki_scheme, host=wiki_hostname), follow_redirects=True):
    """ Gets an article if giving a path to a 404,
        raises NotFoundException, otherwise http exception
    :param path: (either complete (url or just the path) to the article
    :return: Article object
    >>> print article('/wiki/Human').first_link
    /wiki/Hominini
    >>> print article('http://en.wikipedia.org/wiki/Wikipedia:Getting_to_Philosophy').first_link
    /wiki/Hyperlink
    >>> print article('en.wikipedia.org/wiki/Wikipedia:Getting_to_Philosophy').first_link
    /wiki/Hyperlink
    >>> print article('en.wikipedia.org/wiki/Wikipedia:Getting_to_Philosophy1') #doctest: +IGNORE_EXCEPTION_DETAIL
    Traceback (most recent call last):
      ...
    NotFoundException:
    """
    if isinstance(source, Article):
        return source
    if not source.startswith('/'): # If not complete path make sure its either a complete or semi-complete url.
        if source.startswith('http'):
            assert source.startswith(wiki_site + wiki_article_path) # make sure its a complete url
            source = source[len(wiki_site):] # <<< get path
        else:
            assert source.startswith(wiki_hostname + wiki_article_path) # At least make sure it starts with wiki article path
            source = source[len(wiki_hostname):]
    conn = get_or_make_conn()
    conn.request('HEAD', source) # Get a HEAD request first, to test its status code, (404s return ~25KB)
    resp = conn.getresponse()    # but it does mean using up a connection and waiting on IO
    resp.read()
    if follow_redirects:
        while 300 < resp.status < 310:
            source = resp.getheader('location')
            conn.request('HEAD', source)
            resp = conn.getresponse()
            resp.read()
    if resp.status != 200:
        recycle_conn(conn)
        raise NotFoundException('Article Not Found path: {}'.format(source)) if resp.status == 404 else \
            httplib.HTTPException('Non 200 response from : {} status: {} reasons: {}'.format(
                source, resp.status, resp.reason or httplib.responses.get(resp.status, None)
        ))
    conn.request('GET', source)
    resp = conn.getresponse()
    root = html.parse(resp, base_url=wiki_site + source).getroot()
    recycle_conn(conn)
    return Article(next(iter_text_links_path(root), None), article_url_tail(source), last_modified_on(root))

# @cached  # disable for now since articles updates are causing havocs ...
def find_philosophy_route(start, history=None):
    """ Finds a route from start (by following the first link of each article) to philosophy,
            returned route terminates with either:
                None: if a dead end has being reached (Article without links)
                target: if it was reached
                last article: before the start of a cycle
                exception: (article doesn't exist, or failed to parse it.)
    :param start: initial starting point see: article (must be complete/semi-complete url or article path)
    :return: orderedict, keys are the article url tails, values actual article objects , iterating yields complete path.
    >>> r = find_philosophy_route(article('http://en.wikipedia.org/wiki/Computer_science'))
    >>> print '->'.join(r)
    Computer_science->Science->Knowledge->Fact->Experience
    >>> r = find_philosophy_route(article('http://en.wikipedia.org/wiki/Science'))
    >>> print 'Science->Knowledge' in '->'.join(r)
    True
    """
    history = history or collections.OrderedDict()  # Initialize history if omitted.
    try:
        start = article(start)
    except Exception as ex:
        logging.exception('Failed to create article for : {}, msg: {}, history: {}'.format(start, ex, '->'.join(itertools.imap(str, history))))
        history[article_url_tail(start)] = ex
        history[ex] = ex
        return history # if failed append exception for cache object, for subsequent requests.
    if start.url_tail in history:  # If start already present in history bail!
        return history
    history[start.url_tail] = start
    if start.url_tail == 'Philosophy': # Target Reached
        return history
    elif start.first_link is None:  # Dead End reached.
        history[None] = None
        return history
    else:
        result = find_philosophy_route(start.first_link, history=history) # get result.
        if result is not history: # <<<< cache hit, slice it # TODO, implement dictionary chaining to reduce cache size.
            history.update(itertools.islice(result.iteritems(), result.keys().index(article_url_tail(start.first_link)), None))
        return history

def started_coroutine(callable):  # Automatically starts a coroutine when first made.
    @functools.wraps(callable)
    def start(*args, **kwargs):
        routine = callable(*args, **kwargs)
        next(routine)
        return routine
    return start

@started_coroutine
def average(average=0, counts=None):
    """ Simulates a running average, yields current average at every update.
    :param average: starting average, defaults to 0
    :param count: starting count, iterator defaults to itertools.count(), 0->1->2 ...
    :return: coroutine.
    >>> avg = average()
    >>> avg.send(1)
    1.0
    >>> avg.send(5)
    3.0
    """
    counts = counts or itertools.count()
    for prev in counts:
        average = ((yield average) + (prev * average))/float(prev + 1) # <<<< multi by prev to get previous sum.

@started_coroutine
def percentage(target, percentage=0, count=None): # Similar to running average but instead yield as a percentage ...
    """ Similar to average, instead it produces the current fractional percentage of taget hits.
    >>> a = percentage(None)
    >>> a.send(None)
    1.0
    >>> a.send(None)
    1.0
    >>> a.send(None)
    1.0
    >>> a.send(0)
    0.75
    >>> a.send(0)
    0.6
    """
    counts = count or itertools.count()
    for total in counts:
        percentage = ((percentage * total) + ((yield percentage) == target))/float(total + 1)

stats = {
    'count': 0,
    'philosophy': {'average_length': 0},
    'distribution': {
        'philosophy': 0,
        'cycled': 0,
        'dead_end': 0,
        'errors': 0
    }
}


def gather_stats(stats=stats):
    rand_routes = itertools.imap(find_philosophy_route, itertools.imap(apply, itertools.repeat(rand_article_path)))
    count = stats['count']
    make_count = functools.partial(itertools.count, count)
    calc_avg = average(stats['philosophy']['average_length'], make_count())
    expception_type = type('', (object,), {'__eq__': lambda self, other: isinstance(other, Exception)})()
    default = object()
    cycled_type = type('', (object,), {'__eq__': lambda self, other: getattr(route[other], 'first_link', default) in route})()
    distribution = stats['distribution']
    percentages = {
        'philosophy': percentage('Philosophy', distribution['philosophy'], make_count()),
        'dead_end': percentage(None, distribution['dead_end'], make_count()),
        'errors': percentage(expception_type, distribution['errors'], make_count()),
        'cycled': percentage(cycled_type, distribution['cycled'], make_count())
    }
    for route in itertools.ifilter(bool, rand_routes):
        stats['count'] += 1
        last_node = next(reversed(route))
        if last_node == 'Philosophy':
            stats['philosophy']['average_length'] = calc_avg.send(len(route) - 1)
        for name, func in percentages.iteritems():
            distribution[name] = func.send(last_node)

@bottle.route('/')
def get_stats():
    return stats


saved_stats_file = 'analytics.json'
@atexit.register # <<<< At exit save stats ...
def save_stats():
    json.dump(stats, open(saved_stats_file, 'w'))

def start(host='localhost', port=8080, stats=stats):
    thread = threading.Thread(target=gather_stats, args=(stats,))
    thread.daemon = True # <<< TODO: decide whether or not we should do any house keeping before pulling the plug.
    thread.start()
    bottle.run(host=host, port=port)

def config_server():
    global stats, saved_stats_file
    parser = argparse.ArgumentParser(description='Wiki Getting to Philosophy Stats.')
    parser.add_argument('--host', type=str, nargs='?', default='localhost',
                   help='host name or address to listen to defaults to localhost')
    parser.add_argument('--port', type=int, nargs='?', default=8080,
                        help='port address to listen for, defaults to 8080')
    parser.add_argument('--stats', type=str, nargs='?', default=saved_stats_file,
                      help='stats json file path to work with will load the stats if present, and dump the stats on exit')

    args = parser.parse_args()
    saved_stats_file = args.stats
    if os.path.isfile(saved_stats_file):
        stats = json.load(open(saved_stats_file)) # TODO: use a safer method!
    start(args.host, args.port, stats)

if __name__ == '__main__':
    config_server()
