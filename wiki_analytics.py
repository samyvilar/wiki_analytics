__author__ = 'samyvilar'

# Calculate the average number of clicks from a random articles to philosophy.

import sys
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
conn_pool = Queue.Queue(conn_pool_size)

def get_or_make_conn(timeout=None): # Get or Make an http connection
    if timeout is not None:
        return httplib.HTTPConnection(wiki_hostname, wiki_port, timeout=timeout)
    try:
        return conn_pool.get_nowait()
    except Queue.Empty:
        return httplib.HTTPConnection(wiki_hostname, wiki_port)


def recycle_conn(conn):
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

# Bad: http://en.wikipedia.org/wiki/Human
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

@cached
def article(source=None, wiki_site='{scheme}://{host}'.format(scheme=wiki_scheme, host=wiki_hostname)):
    """ Gets an article object DOES NOT FOLLOW REDIRECTS, if giving a path to a 404,
        raises NotFoundException
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

@cached(key=lambda start, target=article('/wiki/Philosophy'), history=None: (start, target))
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
    >>> print '->'.join(r)
    Science->Knowledge->Fact->Experience
    """
    history = history or collections.OrderedDict()  # Initialize history if omitted.
    try:
        start = article(start)
    except Exception as ex:
        logging.exception('Failed to create article for : {}, msg: {}, history: {}'.format(start, ex, '->'.join(itertools.imap(str, history))))
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
def running_average(average=0, counts=None):
    """ Simulates a running average, yields current average at every update.
    :param average: starting average, defaults to 0
    :param count: starting count, iterator defaults to itertools.count(), 0->1->2 ...
    :return: coroutine.
    >>> avg = running_average()
    >>> avg.send(1)
    1.0
    >>> avg.send(5)
    3.0
    """
    counts = counts or itertools.count()
    for seen in counts:
        average = ((yield average) + (seen * average))/float(seen + 1)

philosophy_routes_count = 0

@started_coroutine
def average_route_length(seen=None, target='Philosophy', current_avg=None):
    """ Tracks the running average of the length of the unique routes that end with target.
        yields current average at every update.
    :param routes: sequence of routes
    :param seen: container to keep track of already seen nodes
    :return: coroutine
    >>> routes = [xrange(-5, 10), xrange(10), xrange(1), xrange(10)]
    >>> avg = average_route_length(target=9)
    >>> print [avg.send(r) for r in routes][-1]
    11.5
    """
    default = object() # use a unique object in case seq is empty, to reduce likely hood of collision
    seen = set() if seen is None else seen
    target_reached = lambda seq: next(reversed(seq), default) == target
    calc_average = current_avg or running_average()
    avg = None
    global philosophy_routes_count
    while True:
        route = (yield avg)
        first_node = next(iter(route), default)
        if first_node is not default and first_node not in seen and target_reached(route): # TODO: deal with modified routes!
            seen.add(first_node)
            avg = calc_average.send(len(route) - 1) # exclude starting point.
            philosophy_routes_count += 1

current_average = None
count = 0

def calc_average():
    global current_average, count  # TODO, use safer method than global variables.
    chunks = 1
    routes = itertools.imap(find_philosophy_route, itertools.imap(apply, itertools.repeat(rand_article_path)))
    chunks = itertools.starmap(itertools.islice, itertools.repeat((routes, None, chunks)))
    averages = average_route_length()
    for chunk in chunks:
        for route in chunk:
            current_average = averages.send(route)
            count += 1


@bottle.route('/')
def get_stats():
    return {'routes': {'seen': count},
            'philosophy': {'average_length': current_average, 'count': philosophy_routes_count}}


def start():
    thread = threading.Thread(target=calc_average)
    thread.daemon = True
    thread.start()
    bottle.run(host='localhost', port=8080)

if __name__ == '__main__':
    start()
