#! /usr/bin/env python
__author__ = 'samyvilar'

import os
import argparse
import functools
import itertools
import collections
import httplib
import urlparse
import Queue
import logging
import datetime
import threading
import time
import json
import atexit
import operator

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
    """ Gets a connection from the current pool or makes one if empty or giving a default timeout.
        @@ NOTE that if the connection object isn't reused withing 5 seconds it will be closed, by the wikipedia server!
    :return: conn object.
    >>> conn = get_or_make_conn()
    >>> conn.request('HEAD', '/wiki/Philosophy')
    >>> resp = conn.getresponse()
    >>> r = resp.read() # <<<< response must be consumed befored recycling!
    >>> recycle_conn(conn)
    >>> conn1 = get_or_make_conn()
    >>> assert conn1 is conn # <<<< reuses previous connection.
    >>> conn.request('GET', '/wiki/Computer_Science')
    >>> resp = conn.getresponse()
    >>> _ = resp.read()
    >>> recycle_conn(conn)
    >>> time.sleep(6) # <<<< changing this to 5 will not yield an exception
    >>> conn = get_or_make_conn()
    >>> conn.request('HEAD', '/wiki/Computer_Science')
    >>> resp = conn.getresponse() #doctest: +IGNORE_EXCEPTION_DETAIL
    Traceback (most recent call last):
      ...
    BadStatusLine:
    """
    if timeout is not None:  # If default is giving then we cant used conns from pool
        return make(timeout=timeout)
    try:
        return conn_pool.get_nowait() # TODO: reset connections or send KEEP-ALIVE conns idling more than 5 seconds ...
    except Queue.Empty:
        return make()


def recycle_conn(conn): # To be used when multi-threading support is added
    try:
        conn_pool.put_nowait(conn)
    except Queue.Full:
        conn.close()

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


def rand_article_path(wiki_special_rand_path=wiki_article_path + 'Special:Random'):
    conn = get_or_make_conn()
    conn.request('HEAD', wiki_special_rand_path)
    resp = conn.getresponse()
    location = resp.getheader('location')  # TODO: deal with missing location header!
    _ = resp.read()
    recycle_conn(conn)
    return urlparse.urlparse(location).path


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
    >>> type(last_modified_on(lxml.html.parse('http://en.wikipedia.org/wiki/States_and_territories_of_India').getroot()))
    <type 'datetime.datetime'>
    """
    format_error = functools.partial(
        'Failed to get wiki article last modified date time, url: {url}, error: {er}'.format,
         url=origin.base_url
    )
    try:
        return datetime.datetime.strptime(origin.get_element_by_id(elem_id).text, parsing_format)
    except (KeyError, ValueError) as er:
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
        else:
            logging.warning('Unable to determine wiki article url: {} last modified date time.'.format(origin.base_url))

def iter_text_links_path(origin, elem_id='mw-content-text', from_url=None): # TODO: deal with red links.
    """ Iterate over all the links from a wikipedias text:
        according to http://en.wikipedia.org/wiki/Wikipedia:Getting_to_Philosophy
            take only those links that are non-parenthesized, non-italicized
            while ignoring external links, links to the current page, [or red links (weakly!) supported]
    :param origin: root html node.
    :param elem_id: container id to search within, defaults to 'mw-content-text',
        must be updated if/when wikipedia changes their template
    :return: iterator of links (as they appear in the text)
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
        paren_count = 0 # Assumes that the paren do NOT cross paragraph <p> tags and aren't malformed.
        for node in p.iterchildren():
            if node.tag == 'a' and not paren_count and node.find('i') is None: # non-parenthesize/non-italized link.
                link = node.get('href', '')
                url = urlparse.urlparse(link)
                netloc = url.netloc or wiki_hostname
                path = url.path or current_path
                if not (netloc != wiki_hostname or path == current_path or 'redlink=1' in url.query):
                    yield link  # ignore external/self/red links
            text = node.tail or ''
            for char in text: # <<<< Explore text, count number of open/close parenthesis.
                if char == '(':
                    paren_count += 1
                elif char == ')':
                    paren_count -= 1


Article = collections.namedtuple('Article', ('first_link', 'url_tail', 'modified_on'))

class NotFoundException(httplib.HTTPException):
    pass


def article(source=None, wiki_site='{scheme}://{host}'.format(scheme=wiki_scheme, host=wiki_hostname), follow_redirects=True):
    """ Gets an article if giving a path leads to a 404,
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
    >>> print article('http://en.wikipedia.org/wiki/computer_science').url_tail
    Computer_science
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
    # Get a HEAD request first, to test its status code, (404s return ~25KB)
    #   on the other hand it doesn't guarantee it since the article can be deleted in between calls.
    #   and we are waiting on IO, TODO: set up timings for comparisons.
    conn.request('HEAD', source)
    resp = conn.getresponse()
    _ = resp.read()
    if follow_redirects:
        while 300 < resp.status < 310: # TODO, bound redirects, test redirects.
            source = resp.getheader('location')
            conn.request('HEAD', source)
            resp = conn.getresponse()
            _ = resp.read()
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
    >>> print 'Computer_science->Science->Knowledge' in '->'.join(r)
    True
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
def average(start=0.0, counts=None):
    """ Simulates a running average, yields current average at every update.
    :param start: starting average, defaults to 0.0
    :param counts: iterator/number, defaults to itertools.count(), 0->1->2 ...
    :return: coroutine.
    >>> avg = average()
    >>> avg.send(1)
    1.0
    >>> avg.send(5)
    3.0
    >>> avg = average(counts=9)
    >>> avg.send(1)
    0.1
    """
    if isinstance(counts, (int, long, float)):  # If number initialize counter.
        counts = itertools.count(counts, 1.0)
    counts = counts or itertools.count(0.0, 1.0)
    for count in counts:
        start = ((start * count) + (yield start))/(count + 1.0) # <<<< multi by prev to get previous sum.

@started_coroutine
def percentage(start=0.0, counts=None, match=bool):
    """ Similar to average, instead it produces the current percentage (fractional) of the times match returned True.
    >>> a = percentage(match=lambda other: other is None)
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
    if isinstance(counts, (int, long, float)):
        counts = itertools.count(counts, 1.0)
    counts = counts or itertools.count(0.0, 1.0)
    for prev in counts:
        start = ((start * prev) + match((yield start)))/(prev + 1.0)


stats = {
    'count': 0,
    'last_minute_count': 0,
    'philosophy': {'average_length': 0.0},
    'distribution': {'philosophy': 0.0, 'cycled': 0.0, 'dead_end': 0.0, 'errors': 0.0}
}


def rand_routes(): # Generates random routes from randomly selected articles ...
    for route in itertools.imap(find_philosophy_route, itertools.imap(apply, itertools.repeat(rand_article_path))):
        yield route


shutting_down = threading.Event()

def gather_stats(stats=stats):
    count = stats['count']
    make_count = functools.partial(itertools.count, count)
    calc_avg = average(stats['philosophy']['average_length'], make_count())
    default = object()
    distribution = stats['distribution']
    percentages = {
        'philosophy': percentage(distribution['philosophy'], make_count(),
                                 match=functools.partial(operator.eq, 'Philosophy')),
        'dead_end': percentage(distribution['dead_end'], make_count(),
                               match=functools.partial(operator.is_, None)),
        'cycled': percentage(distribution['cycled'], make_count(),
                             match=lambda node: getattr(route[node], 'first_link', default) in route),
        'errors': percentage(distribution['errors'], make_count(),
                             match=lambda node: isinstance(node, Exception))
    }
    start, last_minute_count = time.time(), 0
    for route in rand_routes():
        if time.time() - start > 60:
            stats['last_minute_count'] = last_minute_count
            start, last_minute_count = time.time(), 0
        stats['count'] += 1
        last_node = next(reversed(route))
        if last_node == 'Philosophy':
            stats['philosophy']['average_length'] = calc_avg.send(len(route) - 1)
        for name, func in percentages.iteritems():
            distribution[name] = func.send(last_node)
        if shutting_down.is_set():
            break
        last_minute_count += 1



@bottle.route('/')
def get_stats():
    return stats

stats_thread = None
saved_stats_file = 'analytics.json'
@atexit.register # <<<< At exit save stats ...
def save_stats():
    if stats_thread:  # if sub threaded started try to safely shut it down before saving stats ...
        shutting_down.set()
        stats_thread.join() # wait until the main thread shuts down so as to avoid the stats object being corrupted
        json.dump(stats, open(saved_stats_file, 'w'))


def start(host='localhost', port=8080, stats=stats):
    global stats_thread
    stats_thread = threading.Thread(target=gather_stats, args=(stats,), name='gather_stats')
    stats_thread.daemon = True # <<< TODO: decide whether or not we should do any house keeping before pulling the plug.
    stats_thread.start()
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
