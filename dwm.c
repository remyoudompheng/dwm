/* See LICENSE file for copyright and license details.
 *
 * dynamic window manager is designed like any other X client as well. It is
 * driven through handling X events. In contrast to other X clients, a window
 * manager selects for SubstructureRedirectMask on the root window, to receive
 * events about window (dis-)appearance.  Only one X connection at a time is
 * allowed to select for this event mask.
 *
 * The event handlers of dwm are organized in an array which is accessed
 * whenever a new event has been fetched. This allows event dispatching
 * in O(1) time.
 *
 * Each child of the root window is called a client, except windows which have
 * set the override_redirect flag.  Clients are organized in a linked client
 * list on each monitor, the focus history is remembered through a stack list
 * on each monitor. Each client contains a bit array to indicate the tags of a
 * client.
 *
 * Keys and tagging rules are organized as arrays and defined in config.h.
 *
 * To understand everything else, start reading main().
 */
#include <errno.h>
#include <locale.h>
#include <stdarg.h>
#include <signal.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <X11/cursorfont.h>
#include <X11/keysymdef.h>
#include <X11/Xatom.h>
#include <X11/Xlib.h>
#include <X11/Xproto.h>
#include <X11/Xutil.h>
#ifdef XINERAMA
#include <X11/extensions/Xinerama.h>
#endif /* XINERAMA */

#include <xcb/xcb.h>
#include <xcb/xcb_icccm.h>
#include <xcb/xcb_keysyms.h>

/* macros */
#define BUTTONMASK              (ButtonPressMask|ButtonReleaseMask)
#define CLEANMASK(mask)         (mask & ~(numlockmask|LockMask))
#define INRECT(X,Y,RX,RY,RW,RH) ((X) >= (RX) && (X) < (RX) + (RW) && (Y) >= (RY) && (Y) < (RY) + (RH))
#define ISVISIBLE(C)            ((C->tags & C->mon->tagset[C->mon->seltags]))
#define LENGTH(X)               (sizeof X / sizeof X[0])
#define MAX(A, B)               ((A) > (B) ? (A) : (B))
#define MIN(A, B)               ((A) < (B) ? (A) : (B))
#define MOUSEMASK               (BUTTONMASK|PointerMotionMask)
#define WIDTH(X)                ((X)->w + 2 * (X)->bw)
#define HEIGHT(X)               ((X)->h + 2 * (X)->bw)
#define TAGMASK                 ((1 << LENGTH(tags)) - 1)
#define TEXTW(X)                (textnw(X, strlen(X)) + dc.font.height)

#define XCB_CONFIG_MOVERESIZE   (XCB_CONFIG_WINDOW_X | XCB_CONFIG_WINDOW_Y | XCB_CONFIG_WINDOW_WIDTH | XCB_CONFIG_WINDOW_HEIGHT)

/* enums */
enum { CurNormal, CurResize, CurMove, CurLast };        /* cursor */
enum { ColBorder, ColFG, ColBG, ColLast };              /* color */
enum { NetSupported, NetWMName, NetLast };              /* EWMH atoms */
enum { WMProtocols, WMDelete, WMState, WMLast };        /* default atoms */
enum { ClkTagBar, ClkLtSymbol, ClkStatusText, ClkWinTitle,
       ClkClientWin, ClkRootWin, ClkLast };             /* clicks */

typedef union {
  int i;
  unsigned int ui;
  float f;
  const void *v;
} Arg;

typedef struct {
  unsigned int click;
  uint16_t mask;
  xcb_button_t button;
  void (*func)(const Arg *arg);
  const Arg arg;
} Button;

typedef struct Monitor Monitor;
typedef struct Client Client;
struct Client {
  char name[256];
  float mina, maxa;
  uint32_t x, y, w, h;
  int basew, baseh, incw, inch, maxw, maxh, minw, minh;
  uint32_t bw, oldbw;
  unsigned int tags;
  Bool isfixed, isfloating, isurgent;
  Client *next;
  Client *snext;
  Monitor *mon;
  Window win;
};

typedef struct {
  int x, y, w, h;
  unsigned long norm[ColLast];
  unsigned long sel[ColLast];
  Drawable drawable;
  GC gc;
  struct {
    int ascent;
    int descent;
    int height;
    XFontSet set;
    XFontStruct *xfont;
  } font;
} DC; /* draw context */

typedef struct {
  uint16_t mod;
  xcb_keysym_t keysym;
  void (*func)(const Arg *);
  const Arg arg;
} Key;

typedef struct {
  const char *symbol;
  void (*arrange)(Monitor *);
} Layout;

struct Monitor {
  char ltsymbol[16];
  float mfact;
  int num;
  int by;               /* bar geometry */
  int mx, my, mw, mh;   /* screen size */
  int wx, wy, ww, wh;   /* window area  */
  unsigned int seltags;
  unsigned int sellt;
  unsigned int tagset[2];
  Bool showbar;
  Bool topbar;
  Client *clients;
  Client *sel;
  Client *stack;
  Monitor *next;
  xcb_window_t barwin;
  const Layout *lt[2];
};

typedef struct {
  const char *class;
  const char *instance;
  const char *title;
  unsigned int tags;
  Bool isfloating;
  int monitor;
} Rule;

/* function declarations */
static void applyrules(Client *c);
static Bool applysizehints(Client *c, int *x, int *y, int *w, int *h, Bool interact);
static void arrange(Monitor *m);
static void arrangemon(Monitor *m);
static void attach(Client *c);
static void attachstack(Client *c);
static void buttonpress(xcb_generic_event_t *e);
static void checkotherwm(void);
static void cleanup(void);
static void cleanupmon(Monitor *mon);
static void clearurgent(Client *c);
static void configure(Client *c);
static void configurenotify(xcb_generic_event_t *e);
static void configurerequest(xcb_generic_event_t *e);
static Monitor *createmon(void);
static void destroynotify(xcb_generic_event_t *e);
static void detach(Client *c);
static void detachstack(Client *c);
static void die(const char *errstr, ...);
static Monitor *dirtomon(int dir);
static void drawbar(Monitor *m);
static void drawbars(void);
static void drawsquare(Bool filled, Bool empty, Bool invert, unsigned long col[ColLast]);
static void drawtext(const char *text, unsigned long col[ColLast], Bool invert);
static void enternotify(xcb_generic_event_t *e);
static void expose(xcb_generic_event_t *e);
static void focus(Client *c);
static void focusin(xcb_generic_event_t *e);
static void focusmon(const Arg *arg);
static void focusstack(const Arg *arg);
static unsigned long getcolor(const char *colstr);
static Bool getrootptr(int *x, int *y);
static long getstate(Window w);
static Bool gettextprop(Window w, Atom atom, char *text, unsigned int size);
static void grabbuttons(Client *c, Bool focused);
static void grabkeys(void);
static void initfont(const char *fontstr);
static Bool isprotodel(Client *c);
static void keypress(xcb_generic_event_t *e);
static void killclient(const Arg *arg);
static void manage(xcb_window_t w, XWindowAttributes *wa);
static void mappingnotify(xcb_generic_event_t *e);
static void maprequest(xcb_generic_event_t *e);
static void monocle(Monitor *m);
static void movemouse(const Arg *arg);
static Client *nexttiled(Client *c);
static Monitor *ptrtomon(int x, int y);
static void propertynotify(xcb_generic_event_t *e);
static void quit(const Arg *arg);
static void resize(Client *c, int x, int y, int w, int h, Bool interact);
static void resizemouse(const Arg *arg);
static void restack(Monitor *m);
static void run(void);
static void scan(void);
static void sendmon(Client *c, Monitor *m);
static void setclientstate(Client *c, long state);
static void setlayout(const Arg *arg);
static void setmfact(const Arg *arg);
static void setup(void);
static void showhide(Client *c);
static void sigchld(int unused);
static void spawn(const Arg *arg);
static void tag(const Arg *arg);
static void tagmon(const Arg *arg);
static int textnw(const char *text, unsigned int len);
static void tile(Monitor *);
static void togglebar(const Arg *arg);
static void togglefloating(const Arg *arg);
static void toggletag(const Arg *arg);
static void toggleview(const Arg *arg);
static void unfocus(Client *c);
static void unmanage(Client *c, Bool destroyed);
static void unmapnotify(xcb_generic_event_t *e);
static Bool updategeom(void);
static void updatebarpos(Monitor *m);
static void updatebars(void);
static void updatenumlockmask(void);
static void updatesizehints(Client *c);
static void updatestatus(void);
static void updatetitle(Client *c);
static void updatewmhints(Client *c);
static void view(const Arg *arg);
static void viewnext(const Arg *arg);
static void viewprev(const Arg *arg);
static Client *wintoclient(Window w);
static Monitor *wintomon(Window w);
static int xerror(Display *dpy, XErrorEvent *ee);
static int xerrordummy(Display *dpy, XErrorEvent *ee);
static void zoom(const Arg *arg);

/* variables */
static const char broken[] = "broken";
static char stext[256];
static xcb_screen_t *screen;  /* X display screen structure */
/* X display screen geometry width, height */
#define sw (screen->width_in_pixels)
#define sh (screen->height_in_pixels)
static int bh, blw = 0;      /* bar geometry */
static int (*xerrorxlib)(Display *, XErrorEvent *);
static unsigned int numlockmask = 0;
static xcb_key_symbols_t *keysyms = 0;
static void (*handler[LASTEvent]) (xcb_generic_event_t *) = {
  [XCB_BUTTON_PRESS] = buttonpress,
  [XCB_CONFIGURE_REQUEST] = configurerequest,
  [XCB_CONFIGURE_NOTIFY] = configurenotify,
  [XCB_DESTROY_NOTIFY] = destroynotify,
  [XCB_ENTER_NOTIFY] = enternotify,
  [XCB_EXPOSE] = expose,
  [XCB_FOCUS_IN] = focusin,
  [XCB_KEY_PRESS] = keypress,
  [XCB_MAPPING_NOTIFY] = mappingnotify,
  [XCB_MAP_REQUEST] = maprequest,
  [XCB_PROPERTY_NOTIFY] = propertynotify,
  [XCB_UNMAP_NOTIFY] = unmapnotify
};
static xcb_atom_t wmatom[WMLast], netatom[NetLast];
static Bool running = True;
static xcb_cursor_t cursor[CurLast];
static Display *dpy;
static xcb_connection_t *xcb_dpy;
static DC dc;
static Monitor *mons = NULL, *selmon = NULL;
static xcb_window_t root;

/* configuration, allows nested code to access above variables */
#include "config.h"

/* compile-time check if all tags fit into an unsigned int bit array. */
struct NumTags { char limitexceeded[LENGTH(tags) > 31 ? -1 : 1]; };

/* convenience wrapper */
void xcb_raise_window(xcb_connection_t *conn, xcb_window_t w) {
  uint32_t mode[] = { XCB_STACK_MODE_ABOVE };
  xcb_configure_window(conn, w, XCB_CONFIG_WINDOW_STACK_MODE, mode);
}

/* function implementations */
void
applyrules(Client *c) {
  const char *class, *instance;
  unsigned int i;
  const Rule *r;
  Monitor *m;
  xcb_get_property_cookie_t cookie;
  xcb_get_wm_class_reply_t ch;

  /* rule matching */
  c->isfloating = c->tags = 0;

  cookie = xcb_get_wm_class_unchecked(xcb_dpy, c->win);

  if(xcb_get_wm_class_reply(xcb_dpy, cookie, &ch, NULL)) {
    class = ch.class_name ? ch.class_name : broken;
    instance = ch.instance_name ? ch.instance_name : broken;
    for(i = 0; i < LENGTH(rules); i++) {
      r = &rules[i];
      if((!r->title || strstr(c->name, r->title))
	 && (!r->class || strstr(class, r->class))
	 && (!r->instance || strstr(instance, r->instance)))
	{
	  c->isfloating = r->isfloating;
	  c->tags |= r->tags;
	  for(m = mons; m && m->num != r->monitor; m = m->next);
	  if(m)
	    c->mon = m;
	}
    }
  }
  xcb_get_wm_class_reply_wipe(&ch);
  c->tags = c->tags & TAGMASK ? c->tags & TAGMASK : c->mon->tagset[c->mon->seltags];
}

Bool
applysizehints(Client *c, int *x, int *y, int *w, int *h, Bool interact) {
  Bool baseismin;
  Monitor *m = c->mon;

  /* set minimum possible */
  *w = MAX(1, *w);
  *h = MAX(1, *h);
  if(interact) {
    if(*x > sw)
      *x = sw - WIDTH(c);
    if(*y > sh)
      *y = sh - HEIGHT(c);
    if(*x + *w + 2 * c->bw < 0)
      *x = 0;
    if(*y + *h + 2 * c->bw < 0)
      *y = 0;
  }
  else {
    if(*x > m->mx + m->mw)
      *x = m->mx + m->mw - WIDTH(c);
    if(*y > m->my + m->mh)
      *y = m->my + m->mh - HEIGHT(c);
    if(*x + *w + 2 * c->bw < m->mx)
      *x = m->mx;
    if(*y + *h + 2 * c->bw < m->my)
      *y = m->my;
  }
  if(*h < bh)
    *h = bh;
  if(*w < bh)
    *w = bh;
  if(resizehints || c->isfloating) {
    /* see last two sentences in ICCCM 4.1.2.3 */
    baseismin = c->basew == c->minw && c->baseh == c->minh;
    if(!baseismin) { /* temporarily remove base dimensions */
      *w -= c->basew;
      *h -= c->baseh;
    }
    /* adjust for aspect limits */
    if(c->mina > 0 && c->maxa > 0) {
      if(c->maxa < (float)*w / *h)
	*w = *h * c->maxa + 0.5;
      else if(c->mina < (float)*h / *w)
	*h = *w * c->mina + 0.5;
    }
    if(baseismin) { /* increment calculation requires this */
      *w -= c->basew;
      *h -= c->baseh;
    }
    /* adjust for increment value */
    if(c->incw)
      *w -= *w % c->incw;
    if(c->inch)
      *h -= *h % c->inch;
    /* restore base dimensions */
    *w += c->basew;
    *h += c->baseh;
    *w = MAX(*w, c->minw);
    *h = MAX(*h, c->minh);
    if(c->maxw)
      *w = MIN(*w, c->maxw);
    if(c->maxh)
      *h = MIN(*h, c->maxh);
  }
  return *x != c->x || *y != c->y || *w != c->w || *h != c->h;
}

void
arrange(Monitor *m) {
  if(m)
    showhide(m->stack);
  else for(m = mons; m; m = m->next)
	 showhide(m->stack);
  focus(NULL);
  if(m)
    arrangemon(m);
  else for(m = mons; m; m = m->next)
	 arrangemon(m);
}

void
arrangemon(Monitor *m) {
  strncpy(m->ltsymbol, m->lt[m->sellt]->symbol, sizeof m->ltsymbol);
  if(m->lt[m->sellt]->arrange)
    m->lt[m->sellt]->arrange(m);
  restack(m);
}

void
attach(Client *c) {
  c->next = c->mon->clients;
  c->mon->clients = c;
}

void
attachstack(Client *c) {
  c->snext = c->mon->stack;
  c->mon->stack = c;
}

void
buttonpress(xcb_generic_event_t *e) {
  unsigned int i, x, click;
  Arg arg = {0};
  Client *c;
  Monitor *m;
  xcb_button_press_event_t *ev = (xcb_button_press_event_t *)e;

  click = ClkRootWin;
  /* focus monitor if necessary */
  if((m = wintomon(ev->event)) && m != selmon) {
    unfocus(selmon->sel);
    selmon = m;
    focus(NULL);
  }
  if(ev->event == selmon->barwin) {
    i = x = 0;
    do {
      x += TEXTW(tags[i]);
    } while(ev->event_x >= x && ++i < LENGTH(tags));
    if(i < LENGTH(tags)) {
      click = ClkTagBar;
      arg.ui = 1 << i;
    }
    else if(ev->event_x < x + blw)
      click = ClkLtSymbol;
    else if(ev->event_x > selmon->wx + selmon->ww - TEXTW(stext))
      click = ClkStatusText;
    else
      click = ClkWinTitle;
  }
  else if((c = wintoclient(ev->event))) {
    focus(c);
    click = ClkClientWin;
  }
  for(i = 0; i < LENGTH(buttons); i++)
    if(click == buttons[i].click && buttons[i].func && buttons[i].button == ev->detail
       && CLEANMASK(buttons[i].mask) == CLEANMASK(ev->state))
      buttons[i].func(click == ClkTagBar && buttons[i].arg.i == 0 ? &arg : &buttons[i].arg);
}

void
checkotherwm(void) {
  /* this causes an error if some other window manager is running */
  uint32_t mask = XCB_EVENT_MASK_SUBSTRUCTURE_REDIRECT;
  xcb_void_cookie_t cookie = xcb_change_window_attributes_checked
    (xcb_dpy, root, XCB_CW_EVENT_MASK, &mask);
  xcb_generic_error_t *error = xcb_request_check(xcb_dpy, cookie);
  if(error != NULL)
    die("dwm: another window manager is already running\n");
}

void
cleanup(void) {
  Arg a = {.ui = ~0};
  Layout foo = { "", NULL };
  Monitor *m;

  view(&a);
  selmon->lt[selmon->sellt] = &foo;
  for(m = mons; m; m = m->next)
    while(m->stack)
      unmanage(m->stack, False);
  if(dc.font.set)
    XFreeFontSet(dpy, dc.font.set);
  else
    XFreeFont(dpy, dc.font.xfont);
  XUngrabKey(dpy, AnyKey, AnyModifier, root);
  xcb_key_symbols_free(keysyms);
  XFreePixmap(dpy, dc.drawable);
  XFreeGC(dpy, dc.gc);
  xcb_free_cursor(xcb_dpy, cursor[CurNormal]);
  xcb_free_cursor(xcb_dpy, cursor[CurResize]);
  xcb_free_cursor(xcb_dpy, cursor[CurMove]);
  while(mons)
    cleanupmon(mons);
  xcb_flush(xcb_dpy);
  XSync(dpy, False);
  XSetInputFocus(dpy, PointerRoot, RevertToPointerRoot, CurrentTime);
}

void
cleanupmon(Monitor *mon) {
  Monitor *m;

  if(mon == mons)
    mons = mons->next;
  else {
    for(m = mons; m && m->next != mon; m = m->next);
    m->next = mon->next;
  }
  xcb_unmap_window(xcb_dpy, mon->barwin);
  xcb_destroy_window(xcb_dpy, mon->barwin);
  free(mon);
}

void
clearurgent(Client *c) {
  xcb_get_property_cookie_t cookie;
  xcb_wm_hints_t       *hints = NULL;

  c->isurgent = False;
  cookie = xcb_get_wm_hints(xcb_dpy, c->win);
  if(!(xcb_get_wm_hints_reply(xcb_dpy, cookie, hints, NULL)))
    return;
  if (hints)
    {
      hints->flags &= ~XCB_WM_HINT_X_URGENCY;
      xcb_set_wm_hints(xcb_dpy, c->win, hints);
      free(hints);
    }
}

void
configure(Client *c) {
  XConfigureEvent ce;

  ce.type = ConfigureNotify;
  ce.display = dpy;
  ce.event = c->win;
  ce.window = c->win;
  ce.x = c->x;
  ce.y = c->y;
  ce.width = c->w;
  ce.height = c->h;
  ce.border_width = c->bw;
  ce.above = None;
  ce.override_redirect = False;
  XSendEvent(dpy, c->win, False, StructureNotifyMask, (XEvent *)&ce);
}

void
configurenotify(xcb_generic_event_t *e) {
  Monitor *m;
  xcb_configure_notify_event_t *ev = (xcb_configure_notify_event_t *)e;
  uint32_t geometry[4];

  if(ev->window == root) {
    sw = ev->width;
    sh = ev->height;
    if(updategeom()) {
      if(dc.drawable != 0)
	XFreePixmap(dpy, dc.drawable);
      dc.drawable = XCreatePixmap(dpy, root, sw, bh, screen->root_depth);
      updatebars();
      for(m = mons; m; m = m->next) {
	geometry[0] = m->wx;
	geometry[1] = m->by;
	geometry[2] = m->ww;
	geometry[3] = bh;
	xcb_configure_window(xcb_dpy, m->barwin, XCB_CONFIG_MOVERESIZE, geometry);
      }
      arrange(NULL);
    }
  }
}

void
configurerequest(xcb_generic_event_t *e) {
  Client *c;
  Monitor *m;
  xcb_configure_request_event_t *ev = (xcb_configure_request_event_t *)e;
  XWindowChanges wc;

  if((c = wintoclient(ev->window))) {
    if(ev->value_mask & CWBorderWidth)
      c->bw = ev->border_width;
    else if(c->isfloating || !selmon->lt[selmon->sellt]->arrange) {
      m = c->mon;
      if(ev->value_mask & CWX)
	c->x = m->mx + ev->x;
      if(ev->value_mask & CWY)
	c->y = m->my + ev->y;
      if(ev->value_mask & CWWidth)
	c->w = ev->width;
      if(ev->value_mask & CWHeight)
	c->h = ev->height;
      if((c->x + c->w) > m->mx + m->mw && c->isfloating)
	c->x = m->mx + (m->mw / 2 - c->w / 2); /* center in x direction */
      if((c->y + c->h) > m->my + m->mh && c->isfloating)
	c->y = m->my + (m->mh / 2 - c->h / 2); /* center in y direction */
      if((ev->value_mask & (CWX|CWY)) && !(ev->value_mask & (CWWidth|CWHeight)))
	configure(c);
      if(ISVISIBLE(c))
	XMoveResizeWindow(dpy, c->win, c->x, c->y, c->w, c->h);
    }
    else
      configure(c);
  }
  else {
    wc.x = ev->x;
    wc.y = ev->y;
    wc.width = ev->width;
    wc.height = ev->height;
    wc.border_width = ev->border_width;
    wc.sibling = ev->sibling;
    wc.stack_mode = ev->stack_mode;
    XConfigureWindow(dpy, ev->window, ev->value_mask, &wc);
  }
  XSync(dpy, False);
}

Monitor *
createmon(void) {
  Monitor *m;

  if(!(m = (Monitor *)calloc(1, sizeof(Monitor))))
    die("fatal: could not malloc() %u bytes\n", sizeof(Monitor));
  m->tagset[0] = m->tagset[1] = 1;
  m->mfact = mfact;
  m->showbar = showbar;
  m->topbar = topbar;
  m->lt[0] = &layouts[0];
  m->lt[1] = &layouts[1 % LENGTH(layouts)];
  strncpy(m->ltsymbol, layouts[0].symbol, sizeof m->ltsymbol);
  return m;
}

void
destroynotify(xcb_generic_event_t *e) {
  Client *c;
  xcb_destroy_notify_event_t *ev = (xcb_destroy_notify_event_t *)e;

  if((c = wintoclient(ev->window)))
    unmanage(c, True);
}

void
detach(Client *c) {
  Client **tc;

  for(tc = &c->mon->clients; *tc && *tc != c; tc = &(*tc)->next);
  *tc = c->next;
}

void
detachstack(Client *c) {
  Client **tc, *t;

  for(tc = &c->mon->stack; *tc && *tc != c; tc = &(*tc)->snext);
  *tc = c->snext;

  if(c == c->mon->sel) {
    for(t = c->mon->stack; t && !ISVISIBLE(t); t = t->snext);
    c->mon->sel = t;
  }
}

void
die(const char *errstr, ...) {
  va_list ap;

  va_start(ap, errstr);
  vfprintf(stderr, errstr, ap);
  va_end(ap);
  exit(EXIT_FAILURE);
}

Monitor *
dirtomon(int dir) {
  Monitor *m = NULL;

  if(dir > 0) {
    if(!(m = selmon->next))
      m = mons;
  }
  else {
    if(selmon == mons)
      for(m = mons; m->next; m = m->next);
    else
      for(m = mons; m->next != selmon; m = m->next);
  }
  return m;
}

void
drawbar(Monitor *m) {
  int x;
  unsigned int i, occ = 0, urg = 0;
  unsigned long *col;
  Client *c;

  for(c = m->clients; c; c = c->next) {
    occ |= c->tags;
    if(c->isurgent)
      urg |= c->tags;
  }
  dc.x = 0;
  for(i = 0; i < LENGTH(tags); i++) {
    dc.w = TEXTW(tags[i]);
    col = m->tagset[m->seltags] & 1 << i ? dc.sel : dc.norm;
    drawtext(tags[i], col, urg & 1 << i);
    drawsquare(m == selmon && selmon->sel && selmon->sel->tags & 1 << i,
	       occ & 1 << i, urg & 1 << i, col);
    dc.x += dc.w;
  }
  dc.w = blw = TEXTW(m->ltsymbol);
  drawtext(m->ltsymbol, dc.norm, False);
  dc.x += dc.w;
  x = dc.x;
  if(m == selmon) { /* status is only drawn on selected monitor */
    dc.w = TEXTW(stext);
    dc.x = m->ww - dc.w;
    if(dc.x < x) {
      dc.x = x;
      dc.w = m->ww - x;
    }
    drawtext(stext, dc.norm, False);
  }
  else
    dc.x = m->ww;
  if((dc.w = dc.x - x) > bh) {
    dc.x = x;
    if(m->sel) {
      col = m == selmon ? dc.sel : dc.norm;
      drawtext(m->sel->name, col, False);
      drawsquare(m->sel->isfixed, m->sel->isfloating, False, col);
    }
    else
      drawtext(NULL, dc.norm, False);
  }
  XCopyArea(dpy, dc.drawable, m->barwin, dc.gc, 0, 0, m->ww, bh, 0, 0);
  XSync(dpy, False);
}

void
drawbars(void) {
  Monitor *m;

  for(m = mons; m; m = m->next)
    drawbar(m);
}

void
drawsquare(Bool filled, Bool empty, Bool invert, unsigned long col[ColLast]) {
  int x;
  XGCValues gcv;
  XRectangle r = { dc.x, dc.y, dc.w, dc.h };

  gcv.foreground = col[invert ? ColBG : ColFG];
  XChangeGC(dpy, dc.gc, GCForeground, &gcv);
  x = (dc.font.ascent + dc.font.descent + 2) / 4;
  r.x = dc.x + 1;
  r.y = dc.y + 1;
  if(filled) {
    r.width = r.height = x + 1;
    XFillRectangles(dpy, dc.drawable, dc.gc, &r, 1);
  }
  else if(empty) {
    r.width = r.height = x;
    XDrawRectangles(dpy, dc.drawable, dc.gc, &r, 1);
  }
}

void
drawtext(const char *text, unsigned long col[ColLast], Bool invert) {
  char buf[256];
  int i, x, y, h, len, olen;
  XRectangle r = { dc.x, dc.y, dc.w, dc.h };

  XSetForeground(dpy, dc.gc, col[invert ? ColFG : ColBG]);
  XFillRectangles(dpy, dc.drawable, dc.gc, &r, 1);
  if(!text)
    return;
  olen = strlen(text);
  h = dc.font.ascent + dc.font.descent;
  y = dc.y + (dc.h / 2) - (h / 2) + dc.font.ascent;
  x = dc.x + (h / 2);
  /* shorten text if necessary */
  for(len = MIN(olen, sizeof buf); len && textnw(text, len) > dc.w - h; len--);
  if(!len)
    return;
  memcpy(buf, text, len);
  if(len < olen)
    for(i = len; i && i > len - 3; buf[--i] = '.');
  XSetForeground(dpy, dc.gc, col[invert ? ColBG : ColFG]);
  if(dc.font.set)
    XmbDrawString(dpy, dc.drawable, dc.font.set, dc.gc, x, y, buf, len);
  else
    XDrawString(dpy, dc.drawable, dc.gc, x, y, buf, len);
}

void
enternotify(xcb_generic_event_t *e) {
  Client *c;
  Monitor *m;
  xcb_enter_notify_event_t *ev = (xcb_enter_notify_event_t *)e;

  if((ev->mode != NotifyNormal || ev->detail == NotifyInferior) && ev->event != root)
    return;
  if((m = wintomon(ev->event)) && m != selmon) {
    unfocus(selmon->sel);
    selmon = m;
  }
  if((c = wintoclient(ev->event)))
    focus(c);
  else
    focus(NULL);
}

void
expose(xcb_generic_event_t *e) {
  Monitor *m;
  xcb_expose_event_t *ev = (xcb_expose_event_t *)e;

  if(ev->count == 0 && (m = wintomon(ev->window)))
    drawbar(m);
}

void
focus(Client *c) {
  if(!c || !ISVISIBLE(c))
    for(c = selmon->stack; c && !ISVISIBLE(c); c = c->snext);
  if(selmon->sel)
    unfocus(selmon->sel);
  if(c) {
    if(c->mon != selmon)
      selmon = c->mon;
    if(c->isurgent)
      clearurgent(c);
    detachstack(c);
    attachstack(c);
    grabbuttons(c, True);
    XSetWindowBorder(dpy, c->win, dc.sel[ColBorder]);
    XSetInputFocus(dpy, c->win, RevertToPointerRoot, CurrentTime);
  }
  else
    XSetInputFocus(dpy, root, RevertToPointerRoot, CurrentTime);
  selmon->sel = c;
  drawbars();
}

void
focusin(xcb_generic_event_t *e) { /* there are some broken focus acquiring clients */
  xcb_focus_in_event_t *ev = (xcb_focus_in_event_t *)e;

  if(selmon->sel && ev->event != selmon->sel->win)
    XSetInputFocus(dpy, selmon->sel->win, RevertToPointerRoot, CurrentTime);
}

void
focusmon(const Arg *arg) {
  Monitor *m = NULL;

  if(!mons->next)
    return;
  m = dirtomon(arg->i);
  unfocus(selmon->sel);
  selmon = m;
  focus(NULL);
}

void
focusstack(const Arg *arg) {
  Client *c = NULL, *i;

  if(!selmon->sel)
    return;
  if(arg->i > 0) {
    for(c = selmon->sel->next; c && !ISVISIBLE(c); c = c->next);
    if(!c)
      for(c = selmon->clients; c && !ISVISIBLE(c); c = c->next);
  }
  else {
    for(i = selmon->clients; i != selmon->sel; i = i->next)
      if(ISVISIBLE(i))
	c = i;
    if(!c)
      for(; i; i = i->next)
	if(ISVISIBLE(i))
	  c = i;
  }
  if(c) {
    focus(c);
    restack(selmon);
  }
}

unsigned long
getcolor(const char *colstr) {
  Colormap cmap = screen->default_colormap;
  XColor color;

  if(!XAllocNamedColor(dpy, cmap, colstr, &color, &color))
    die("error, cannot allocate color '%s'\n", colstr);
  return color.pixel;
}

Bool
getrootptr(int *x, int *y) {
  int di;
  unsigned int dui;
  Window dummy;

  return XQueryPointer(dpy, root, &dummy, &dummy, x, y, &di, &di, &dui);
}

long
getstate(Window w) {
  int format, status;
  long result = -1;
  unsigned char *p = NULL;
  unsigned long n, extra;
  Atom real;

  status = XGetWindowProperty(dpy, w, wmatom[WMState], 0L, 2L, False, wmatom[WMState],
			      &real, &format, &n, &extra, (unsigned char **)&p);
  if(status != Success)
    return -1;
  if(n != 0)
    result = *p;
  XFree(p);
  return result;
}

Bool
gettextprop(Window w, Atom atom, char *text, unsigned int size) {
  char **list = NULL;
  int n;
  XTextProperty name;

  if(!text || size == 0)
    return False;
  text[0] = '\0';
  XGetTextProperty(dpy, w, &name, atom);
  if(!name.nitems)
    return False;
  if(name.encoding == XA_STRING)
    strncpy(text, (char *)name.value, size - 1);
  else {
    if(XmbTextPropertyToTextList(dpy, &name, &list, &n) >= Success && n > 0 && *list) {
      strncpy(text, *list, size - 1);
      XFreeStringList(list);
    }
  }
  text[size - 1] = '\0';
  XFree(name.value);
  return True;
}

void
grabbuttons(Client *c, Bool focused) {
  updatenumlockmask();
  {
    unsigned int i, j;
    unsigned int modifiers[] = { 0, LockMask, numlockmask, numlockmask|LockMask };
    XUngrabButton(dpy, AnyButton, AnyModifier, c->win);
    if(focused) {
      for(i = 0; i < LENGTH(buttons); i++)
	if(buttons[i].click == ClkClientWin)
	  for(j = 0; j < LENGTH(modifiers); j++)
	    XGrabButton(dpy, buttons[i].button,
			buttons[i].mask | modifiers[j],
			c->win, False, BUTTONMASK,
			GrabModeAsync, GrabModeSync, None, None);
    }
    else
      XGrabButton(dpy, AnyButton, AnyModifier, c->win, False,
		  BUTTONMASK, GrabModeAsync, GrabModeSync, None, None);
  }
}

void
grabkeys(void) {
  updatenumlockmask();
  {
    unsigned int i, j;
    unsigned int modifiers[] = { 0, LockMask, numlockmask, numlockmask|LockMask };
    xcb_keycode_t *code;

    xcb_ungrab_key(xcb_dpy, AnyKey, root, AnyModifier);
    for(i = 0; i < LENGTH(keys); i++) {
      if((code = xcb_key_symbols_get_keycode(keysyms, keys[i].keysym)))
	for(j = 0; j < LENGTH(modifiers); j++)
	  xcb_grab_key(xcb_dpy, True, root,
		       keys[i].mod | modifiers[j], code[0],
		       XCB_GRAB_MODE_ASYNC, XCB_GRAB_MODE_ASYNC);
    }
  }
}

void
initfont(const char *fontstr) {
  char *def, **missing;
  int i, n;

  missing = NULL;
  dc.font.set = XCreateFontSet(dpy, fontstr, &missing, &n, &def);
  if(missing) {
    while(n--)
      fprintf(stderr, "dwm: missing fontset: %s\n", missing[n]);
    XFreeStringList(missing);
  }
  if(dc.font.set) {
    XFontSetExtents *font_extents;
    XFontStruct **xfonts;
    char **font_names;

    dc.font.ascent = dc.font.descent = 0;
    font_extents = XExtentsOfFontSet(dc.font.set);
    n = XFontsOfFontSet(dc.font.set, &xfonts, &font_names);
    for(i = 0, dc.font.ascent = 0, dc.font.descent = 0; i < n; i++) {
      dc.font.ascent = MAX(dc.font.ascent, (*xfonts)->ascent);
      dc.font.descent = MAX(dc.font.descent,(*xfonts)->descent);
      xfonts++;
    }
  }
  else {
    if(!(dc.font.xfont = XLoadQueryFont(dpy, fontstr))
       && !(dc.font.xfont = XLoadQueryFont(dpy, "fixed")))
      die("error, cannot load font: '%s'\n", fontstr);
    dc.font.ascent = dc.font.xfont->ascent;
    dc.font.descent = dc.font.xfont->descent;
  }
  dc.font.height = dc.font.ascent + dc.font.descent;
}

Bool
isprotodel(Client *c) {
  int i, n;
  Atom *protocols;
  Bool ret = False;

  if(XGetWMProtocols(dpy, c->win, &protocols, &n)) {
    for(i = 0; !ret && i < n; i++)
      if(protocols[i] == wmatom[WMDelete])
	ret = True;
    XFree(protocols);
  }
  return ret;
}

#ifdef XINERAMA
static Bool
isuniquegeom(XineramaScreenInfo *unique, size_t len, XineramaScreenInfo *info) {
  unsigned int i;

  for(i = 0; i < len; i++)
    if(unique[i].x_org == info->x_org && unique[i].y_org == info->y_org
       && unique[i].width == info->width && unique[i].height == info->height)
      return False;
  return True;
}
#endif /* XINERAMA */

void
keypress(xcb_generic_event_t *e) {
  unsigned int i;
  xcb_keysym_t keysym;
  xcb_key_press_event_t *ev = (xcb_key_press_event_t *)e;

  keysym = xcb_key_symbols_get_keysym(keysyms, ev->detail, 0);
  for(i = 0; i < LENGTH(keys); i++)
    if(keysym == keys[i].keysym
       && CLEANMASK(keys[i].mod) == CLEANMASK(ev->state)
       && keys[i].func)
      keys[i].func(&(keys[i].arg));
}

void
killclient(const Arg *arg) {
  XEvent ev;

  if(!selmon->sel)
    return;
  if(isprotodel(selmon->sel)) {
    ev.type = ClientMessage;
    ev.xclient.window = selmon->sel->win;
    ev.xclient.message_type = wmatom[WMProtocols];
    ev.xclient.format = 32;
    ev.xclient.data.l[0] = wmatom[WMDelete];
    ev.xclient.data.l[1] = CurrentTime;
    XSendEvent(dpy, selmon->sel->win, False, NoEventMask, &ev);
  }
  else {
    XGrabServer(dpy);
    XSetErrorHandler(xerrordummy);
    XSetCloseDownMode(dpy, DestroyAll);
    XKillClient(dpy, selmon->sel->win);
    XSync(dpy, False);
    XSetErrorHandler(xerror);
    XUngrabServer(dpy);
  }
}

void
manage(xcb_window_t w, XWindowAttributes *wa) {
  static Client cz;
  Client *c, *t = NULL;
  Window trans = None;

  if(!(c = malloc(sizeof(Client))))
    die("fatal: could not malloc() %u bytes\n", sizeof(Client));
  *c = cz;
  c->win = w;
  updatetitle(c);
  if(XGetTransientForHint(dpy, w, &trans))
    t = wintoclient(trans);
  if(t) {
    c->mon = t->mon;
    c->tags = t->tags;
  }
  else {
    c->mon = selmon;
    applyrules(c);
  }
  /* geometry */
  c->x = wa->x + c->mon->wx;
  c->y = wa->y + c->mon->wy;
  c->w = wa->width;
  c->h = wa->height;
  c->oldbw = wa->border_width;
  if(c->w == c->mon->mw && c->h == c->mon->mh) {
    c->x = c->mon->mx;
    c->y = c->mon->my;
    c->bw = 0;
  }
  else {
    if(c->x + WIDTH(c) > c->mon->mx + c->mon->mw)
      c->x = c->mon->mx + c->mon->mw - WIDTH(c);
    if(c->y + HEIGHT(c) > c->mon->my + c->mon->mh)
      c->y = c->mon->my + c->mon->mh - HEIGHT(c);
    c->x = MAX(c->x, c->mon->mx);
    /* only fix client y-offset, if the client center might cover the bar */
    c->y = MAX(c->y, ((c->mon->by == 0) && (c->x + (c->w / 2) >= c->mon->wx)
		      && (c->x + (c->w / 2) < c->mon->wx + c->mon->ww)) ? bh : c->mon->my);
    c->bw = borderpx;
  }
  uint32_t bw = c->bw;
  xcb_configure_window(xcb_dpy, c->win, XCB_CONFIG_WINDOW_BORDER_WIDTH, &bw);
  XSetWindowBorder(dpy, w, dc.norm[ColBorder]);
  configure(c); /* propagates border_width, if size doesn't change */
  updatesizehints(c);
  uint32_t ev_mask = XCB_EVENT_MASK_ENTER_WINDOW | XCB_EVENT_MASK_FOCUS_CHANGE |
    XCB_EVENT_MASK_PROPERTY_CHANGE | XCB_EVENT_MASK_STRUCTURE_NOTIFY;
  xcb_change_window_attributes(xcb_dpy, w, XCB_CW_EVENT_MASK, &ev_mask);
  grabbuttons(c, False);
  if(!c->isfloating)
    c->isfloating = trans != None || c->isfixed;
  if(c->isfloating)
    xcb_raise_window(xcb_dpy, c->win);
  attach(c);
  attachstack(c);

  uint32_t geom[4];
  geom[0] = c->x + 2*sw;  /* some windows require this */
  geom[1] = c->y;
  geom[2] = c->w;
  geom[3] = c->h;
  xcb_configure_window(xcb_dpy, c->win, XCB_CONFIG_MOVERESIZE, geom);
  xcb_map_window(xcb_dpy, c->win);
  setclientstate(c, NormalState);
  arrange(c->mon);
}

void
mappingnotify(xcb_generic_event_t *e) {
  xcb_mapping_notify_event_t *ev = (xcb_mapping_notify_event_t *)e;

  xcb_refresh_keyboard_mapping(NULL, ev);
  if(ev->request == XCB_MAPPING_KEYBOARD)
    grabkeys();
}

void
maprequest(xcb_generic_event_t *e) {
  static XWindowAttributes wa;
  xcb_map_request_event_t *ev = (xcb_map_request_event_t *)e;

  if(!XGetWindowAttributes(dpy, ev->window, &wa))
    return;
  if(wa.override_redirect)
    return;
  if(!wintoclient(ev->window))
    manage(ev->window, &wa);
}

void
monocle(Monitor *m) {
  unsigned int n = 0;
  Client *c;

  for(c = m->clients; c; c = c->next)
    if(ISVISIBLE(c))
      n++;
  if(n > 0) /* override layout symbol */
    snprintf(m->ltsymbol, sizeof m->ltsymbol, "[%d]", n);
  for(c = nexttiled(m->clients); c; c = nexttiled(c->next))
    resize(c, m->wx, m->wy, m->ww - 2 * c->bw, m->wh - 2 * c->bw, False);
}

void
movemouse(const Arg *arg) {
  int x, y, ocx, ocy, nx, ny;
  Client *c;
  Monitor *m;
  xcb_generic_event_t *ev;
  xcb_motion_notify_event_t *e;

  if(!(c = selmon->sel))
    return;
  restack(selmon);
  ocx = c->x;
  ocy = c->y;
  if(XGrabPointer(dpy, root, False, MOUSEMASK, GrabModeAsync, GrabModeAsync,
		  None, cursor[CurMove], CurrentTime) != GrabSuccess)
    return;
  if(!getrootptr(&x, &y))
    return;
  do {
    // XCB does not provide an alternative to XMaskEvent
    ev = xcb_wait_for_event(xcb_dpy);
    if (!ev) continue;
    switch (ev->response_type) {
    case ConfigureRequest:
    case Expose:
    case MapRequest:
      handler[ev->response_type](ev);
      break;
    case MotionNotify:
      e = (xcb_motion_notify_event_t *)ev;
      nx = ocx + (e->event_x - x);
      ny = ocy + (e->event_y - y);
      if(snap && nx >= selmon->wx && nx <= selmon->wx + selmon->ww
	 && ny >= selmon->wy && ny <= selmon->wy + selmon->wh) {
	if(abs(selmon->wx - nx) < snap)
	  nx = selmon->wx;
	else if(abs((selmon->wx + selmon->ww) - (nx + WIDTH(c))) < snap)
	  nx = selmon->wx + selmon->ww - WIDTH(c);
	if(abs(selmon->wy - ny) < snap)
	  ny = selmon->wy;
	else if(abs((selmon->wy + selmon->wh) - (ny + HEIGHT(c))) < snap)
	  ny = selmon->wy + selmon->wh - HEIGHT(c);
	if(!c->isfloating && selmon->lt[selmon->sellt]->arrange
	   && (abs(nx - c->x) > snap || abs(ny - c->y) > snap))
	  togglefloating(NULL);
      }
      if(!selmon->lt[selmon->sellt]->arrange || c->isfloating)
	resize(c, nx, ny, c->w, c->h, True);
      break;
    }
  } while(ev->response_type != ButtonRelease);
  XUngrabPointer(dpy, CurrentTime);
  if((m = ptrtomon(c->x + c->w / 2, c->y + c->h / 2)) != selmon) {
    sendmon(c, m);
    selmon = m;
    focus(NULL);
  }
}

Client *
nexttiled(Client *c) {
  for(; c && (c->isfloating || !ISVISIBLE(c)); c = c->next);
  return c;
}

Monitor *
ptrtomon(int x, int y) {
  Monitor *m;

  for(m = mons; m; m = m->next)
    if(INRECT(x, y, m->wx, m->wy, m->ww, m->wh))
      return m;
  return selmon;
}

void
propertynotify(xcb_generic_event_t *e) {
  Client *c;
  Window trans;
  xcb_property_notify_event_t *ev = (xcb_property_notify_event_t *)e;

  if((ev->window == root) && (ev->atom == XA_WM_NAME))
    updatestatus();
  else if(ev->state == PropertyDelete)
    return; /* ignore */
  else if((c = wintoclient(ev->window))) {
    switch (ev->atom) {
    default: break;
    case XA_WM_TRANSIENT_FOR:
      XGetTransientForHint(dpy, c->win, &trans);
      if(!c->isfloating && (c->isfloating = (wintoclient(trans) != NULL)))
	arrange(c->mon);
      break;
    case XA_WM_NORMAL_HINTS:
      updatesizehints(c);
      break;
    case XA_WM_HINTS:
      updatewmhints(c);
      drawbars();
      break;
    }
    if(ev->atom == XA_WM_NAME || ev->atom == netatom[NetWMName]) {
      updatetitle(c);
      if(c == c->mon->sel)
	drawbar(c->mon);
    }
  }
}

void
quit(const Arg *arg) {
  running = False;
}

void
resize(Client *c, int x, int y, int w, int h, Bool interact) {
  uint32_t geom[5];

  if(applysizehints(c, &x, &y, &w, &h, interact)) {
    c->x = geom[0] = x;
    c->y = geom[1] = y;
    c->w = geom[2] = w;
    c->h = geom[3] = h;
    geom[4] = c->bw;
    xcb_configure_window(xcb_dpy, c->win, XCB_CONFIG_MOVERESIZE |
			 XCB_CONFIG_WINDOW_BORDER_WIDTH, geom);
    configure(c);
    xcb_flush(xcb_dpy);
  }
}

void
resizemouse(const Arg *arg) {
  int ocx, ocy;
  int nw, nh;
  Client *c;
  Monitor *m;
  xcb_generic_event_t *ev;
  xcb_motion_notify_event_t *e;

  if(!(c = selmon->sel))
    return;
  restack(selmon);
  ocx = c->x;
  ocy = c->y;
  if(XGrabPointer(dpy, root, False, MOUSEMASK, GrabModeAsync, GrabModeAsync,
		  None, cursor[CurResize], CurrentTime) != GrabSuccess)
    return;
  XWarpPointer(dpy, None, c->win, 0, 0, 0, 0, c->w + c->bw - 1, c->h + c->bw - 1);
  do {
    // XCB does not provide an equivalent for XMaskEvent
    ev = xcb_wait_for_event(xcb_dpy);
    switch(ev->response_type) {
    case ConfigureRequest:
    case Expose:
    case MapRequest:
      handler[ev->response_type](ev);
      break;
    case MotionNotify:
      e = (xcb_motion_notify_event_t *)ev;
      nw = MAX(e->event_x - ocx - 2 * c->bw + 1, 1);
      nh = MAX(e->event_y - ocy - 2 * c->bw + 1, 1);
      if(snap && nw >= selmon->wx && nw <= selmon->wx + selmon->ww
	 && nh >= selmon->wy && nh <= selmon->wy + selmon->wh)
	{
	  if(!c->isfloating && selmon->lt[selmon->sellt]->arrange
	     && (abs(nw - c->w) > snap || abs(nh - c->h) > snap))
	    togglefloating(NULL);
	}
      if(!selmon->lt[selmon->sellt]->arrange || c->isfloating)
	resize(c, c->x, c->y, nw, nh, True);
      break;
    }
  } while(ev->response_type != ButtonRelease);
  XWarpPointer(dpy, None, c->win, 0, 0, 0, 0, c->w + c->bw - 1, c->h + c->bw - 1);
  XUngrabPointer(dpy, CurrentTime);
  // while(XCheckMaskEvent(dpy, EnterWindowMask, &ev));
  if((m = ptrtomon(c->x + c->w / 2, c->y + c->h / 2)) != selmon) {
    sendmon(c, m);
    selmon = m;
    focus(NULL);
  }
}

void
restack(Monitor *m) {
  Client *c;
  XEvent ev;
  XWindowChanges wc;

  drawbar(m);
  if(!m->sel)
    return;
  if(m->sel->isfloating || !m->lt[m->sellt]->arrange)
    XRaiseWindow(dpy, m->sel->win);
  if(m->lt[m->sellt]->arrange) {
    wc.stack_mode = Below;
    wc.sibling = m->barwin;
    for(c = m->stack; c; c = c->snext)
      if(!c->isfloating && ISVISIBLE(c)) {
	XConfigureWindow(dpy, c->win, CWSibling|CWStackMode, &wc);
	wc.sibling = c->win;
      }
  }
  XSync(dpy, False);
  while(XCheckMaskEvent(dpy, EnterWindowMask, &ev));
}

void
run(void) {
  xcb_generic_event_t *ev;

  /* main event loop */
  xcb_flush(xcb_dpy);
  while(running && (ev = xcb_wait_for_event(xcb_dpy)))
    if(handler[ev->response_type])
      handler[ev->response_type](ev); /* call handler */
}

void
scan(void) {
  unsigned int i, num;
  Window d1, d2, *wins = NULL;
  XWindowAttributes wa;

  if(XQueryTree(dpy, root, &d1, &d2, &wins, &num)) {
    for(i = 0; i < num; i++) {
      if(!XGetWindowAttributes(dpy, wins[i], &wa)
	 || wa.override_redirect || XGetTransientForHint(dpy, wins[i], &d1))
	continue;
      if(wa.map_state == IsViewable || getstate(wins[i]) == IconicState)
	manage(wins[i], &wa);
    }
    for(i = 0; i < num; i++) { /* now the transients */
      if(!XGetWindowAttributes(dpy, wins[i], &wa))
	continue;
      if(XGetTransientForHint(dpy, wins[i], &d1)
	 && (wa.map_state == IsViewable || getstate(wins[i]) == IconicState))
	manage(wins[i], &wa);
    }
    if(wins)
      XFree(wins);
  }
}

void
sendmon(Client *c, Monitor *m) {
  if(c->mon == m)
    return;
  unfocus(c);
  detach(c);
  detachstack(c);
  c->mon = m;
  c->tags = m->tagset[m->seltags]; /* assign tags of target monitor */
  attach(c);
  attachstack(c);
  focus(NULL);
  arrange(NULL);
}

void
setclientstate(Client *c, long state) {
  long data[] = { state, None };

  XChangeProperty(dpy, c->win, wmatom[WMState], wmatom[WMState], 32,
		  PropModeReplace, (unsigned char *)data, 2);
}

void
setlayout(const Arg *arg) {
  if(!arg || !arg->v || arg->v != selmon->lt[selmon->sellt])
    selmon->sellt ^= 1;
  if(arg && arg->v)
    selmon->lt[selmon->sellt] = (Layout *)arg->v;
  strncpy(selmon->ltsymbol, selmon->lt[selmon->sellt]->symbol, sizeof selmon->ltsymbol);
  if(selmon->sel)
    arrange(selmon);
  else
    drawbar(selmon);
}

/* arg > 1.0 will set mfact absolutly */
void
setmfact(const Arg *arg) {
  float f;

  if(!arg || !selmon->lt[selmon->sellt]->arrange)
    return;
  f = arg->f < 1.0 ? arg->f + selmon->mfact : arg->f - 1.0;
  if(f < 0.1 || f > 0.9)
    return;
  selmon->mfact = f;
  arrange(selmon);
}

void
setup(void) {
  /* clean up any zombies immediately */
  sigchld(0);

  /* init screen */
  screen = xcb_setup_roots_iterator(xcb_get_setup(xcb_dpy)).data;
  root = screen->root;
  /* check for other WM */
  checkotherwm();
  /* init geometry */
  initfont(font);
  bh = dc.h = dc.font.height + 2;
  updategeom();
  /* get keysyms */
  keysyms = xcb_key_symbols_alloc(xcb_dpy);
  /* init atoms */
  xcb_intern_atom_cookie_t atom_c[5];
  atom_c[0] = xcb_intern_atom_unchecked(xcb_dpy, 0, strlen("WM_PROTOCOLS"), "WM_PROTOCOLS");
  atom_c[1] = xcb_intern_atom_unchecked(xcb_dpy, 0, strlen("WM_DELETE_WINDOW"), "WM_DELETE_WINDOW");
  atom_c[2] = xcb_intern_atom_unchecked(xcb_dpy, 0, strlen("WM_STATE"), "WM_STATE");
  atom_c[3] = xcb_intern_atom_unchecked(xcb_dpy, 0, strlen("_NET_SUPPORTED"), "_NET_SUPPORTED");
  atom_c[4] = xcb_intern_atom_unchecked(xcb_dpy, 0, strlen("_NET_WM_NAME"), "_NET_WM_NAME");

  xcb_intern_atom_reply_t *atom_reply;
  atom_reply = xcb_intern_atom_reply(xcb_dpy, atom_c[0], NULL);
  if(atom_reply) { wmatom[WMProtocols] = atom_reply->atom; free(atom_reply); }
  atom_reply = xcb_intern_atom_reply(xcb_dpy, atom_c[1], NULL);
  if(atom_reply) { wmatom[WMDelete] = atom_reply->atom; free(atom_reply); }
  atom_reply = xcb_intern_atom_reply(xcb_dpy, atom_c[2], NULL);
  if(atom_reply) { wmatom[WMState] = atom_reply->atom; free(atom_reply); }
  atom_reply = xcb_intern_atom_reply(xcb_dpy, atom_c[3], NULL);
  if(atom_reply) { netatom[NetSupported] = atom_reply->atom; free(atom_reply); }
  atom_reply = xcb_intern_atom_reply(xcb_dpy, atom_c[4], NULL);
  if(atom_reply) { netatom[NetWMName] = atom_reply->atom; free(atom_reply); }
  /* init cursors */
  xcb_font_t font = xcb_generate_id (xcb_dpy);
  xcb_open_font(xcb_dpy, font, strlen("cursor"), "cursor");
  cursor[CurNormal] = xcb_generate_id(xcb_dpy);
  cursor[CurResize] = xcb_generate_id(xcb_dpy);
  cursor[CurMove] = xcb_generate_id(xcb_dpy);
  xcb_create_glyph_cursor(xcb_dpy, cursor[CurNormal], font, font,
			  XC_left_ptr, XC_left_ptr + 1, 0,0,0,0,0,0);
  xcb_create_glyph_cursor(xcb_dpy, cursor[CurResize], font, font,
			  XC_sizing, XC_sizing + 1, 0,0,0,0,0,0);
  xcb_create_glyph_cursor(xcb_dpy, cursor[CurMove], font, font,
			  XC_fleur, XC_fleur + 1, 0,0,0,0,0,0);
  xcb_flush(xcb_dpy);
  /* init appearance */
  dc.norm[ColBorder] = getcolor(normbordercolor);
  dc.norm[ColBG] = getcolor(normbgcolor);
  dc.norm[ColFG] = getcolor(normfgcolor);
  dc.sel[ColBorder] = getcolor(selbordercolor);
  dc.sel[ColBG] = getcolor(selbgcolor);
  dc.sel[ColFG] = getcolor(selfgcolor);
  dc.drawable = XCreatePixmap(dpy, root, sw, bh, screen->root_depth);
  dc.gc = XCreateGC(dpy, root, 0, NULL);
  XSetLineAttributes(dpy, dc.gc, 1, LineSolid, CapButt, JoinMiter);
  if(!dc.font.set)
    XSetFont(dpy, dc.gc, dc.font.xfont->fid);
  /* init bars */
  updatebars();
  updatestatus();
  /* EWMH support per view */
  XChangeProperty(dpy, root, netatom[NetSupported], XA_ATOM, 32,
		  PropModeReplace, (unsigned char *) netatom, NetLast);
  /* select for events */
  uint32_t wa;
  wa = cursor[CurNormal];
  xcb_change_window_attributes(xcb_dpy, root, XCB_CW_CURSOR, &wa);
  wa = XCB_EVENT_MASK_SUBSTRUCTURE_REDIRECT | XCB_EVENT_MASK_SUBSTRUCTURE_NOTIFY |
    XCB_EVENT_MASK_BUTTON_PRESS | XCB_EVENT_MASK_ENTER_WINDOW | XCB_EVENT_MASK_LEAVE_WINDOW |
    XCB_EVENT_MASK_STRUCTURE_NOTIFY | XCB_EVENT_MASK_PROPERTY_CHANGE;
  xcb_change_window_attributes(xcb_dpy, root, XCB_CW_EVENT_MASK, &wa);
  grabkeys();
  xcb_flush(xcb_dpy);
}

void
showhide(Client *c) {
  if(!c)
    return;
  uint32_t geom[2];
  if(ISVISIBLE(c)) { /* show clients top down */
    geom[0] = c->x; geom[1] = c->y;
    xcb_configure_window(xcb_dpy, c->win, XCB_CONFIG_WINDOW_X | XCB_CONFIG_WINDOW_Y, geom);
    if(!c->mon->lt[c->mon->sellt]->arrange || c->isfloating)
      resize(c, c->x, c->y, c->w, c->h, False);
    showhide(c->snext);
  }
  else { /* hide clients bottom up */
    showhide(c->snext);
    geom[0] = c->x + 2 * sw; geom[1] = c->y;
    xcb_configure_window(xcb_dpy, c->win, XCB_CONFIG_WINDOW_X | XCB_CONFIG_WINDOW_Y, geom);
  }
}


void
sigchld(int unused) {
  if(signal(SIGCHLD, sigchld) == SIG_ERR)
    die("Can't install SIGCHLD handler");
  while(0 < waitpid(-1, NULL, WNOHANG));
}

void
spawn(const Arg *arg) {
  if(fork() == 0) {
    if(dpy)
      close(ConnectionNumber(dpy));
    setsid();
    execvp(((char **)arg->v)[0], (char **)arg->v);
    fprintf(stderr, "dwm: execvp %s", ((char **)arg->v)[0]);
    perror(" failed");
    exit(0);
  }
}

void
tag(const Arg *arg) {
  if(selmon->sel && arg->ui & TAGMASK) {
    selmon->sel->tags = arg->ui & TAGMASK;
    arrange(selmon);
  }
}

void
tagmon(const Arg *arg) {
  if(!selmon->sel || !mons->next)
    return;
  sendmon(selmon->sel, dirtomon(arg->i));
}

int
textnw(const char *text, unsigned int len) {
  XRectangle r;

  if(dc.font.set) {
    XmbTextExtents(dc.font.set, text, len, NULL, &r);
    return r.width;
  }
  return XTextWidth(dc.font.xfont, text, len);
}

void
tile(Monitor *m) {
  int x, y, h, w, mw;
  unsigned int i, n;
  Client *c;

  for(n = 0, c = nexttiled(m->clients); c; c = nexttiled(c->next), n++);
  if(n == 0)
    return;
  /* master */
  c = nexttiled(m->clients);
  mw = m->mfact * m->ww;
  resize(c, m->wx, m->wy, (n == 1 ? m->ww : mw) - 2 * c->bw, m->wh - 2 * c->bw, False);
  if(--n == 0)
    return;
  /* tile stack */
  x = (m->wx + mw > c->x + c->w) ? c->x + c->w + 2 * c->bw : m->wx + mw;
  y = m->wy;
  w = (m->wx + mw > c->x + c->w) ? m->wx + m->ww - x : m->ww - mw;
  h = m->wh / n;
  if(h < bh)
    h = m->wh;
  for(i = 0, c = nexttiled(c->next); c; c = nexttiled(c->next), i++) {
    resize(c, x, y, w - 2 * c->bw, /* remainder */ ((i + 1 == n)
						    ? m->wy + m->wh - y - 2 * c->bw : h - 2 * c->bw), False);
    if(h != m->wh)
      y = c->y + HEIGHT(c);
  }
}

void
togglebar(const Arg *arg) {
  selmon->showbar = !selmon->showbar;
  updatebarpos(selmon);
  uint32_t geom[4];
  geom[0] = selmon->wx; geom[1] = selmon->by; geom[2] = selmon->ww; geom[3] = bh;
  xcb_configure_window(xcb_dpy, selmon->barwin, XCB_CONFIG_MOVERESIZE, geom);
  arrange(selmon);
}

void
togglefloating(const Arg *arg) {
  if(!selmon->sel)
    return;
  selmon->sel->isfloating = !selmon->sel->isfloating || selmon->sel->isfixed;
  if(selmon->sel->isfloating)
    resize(selmon->sel, selmon->sel->x, selmon->sel->y,
	   selmon->sel->w, selmon->sel->h, False);
  arrange(selmon);
}

void
toggletag(const Arg *arg) {
  unsigned int newtags;

  if(!selmon->sel)
    return;
  newtags = selmon->sel->tags ^ (arg->ui & TAGMASK);
  if(newtags) {
    selmon->sel->tags = newtags;
    arrange(selmon);
  }
}

void
toggleview(const Arg *arg) {
  unsigned int newtagset = selmon->tagset[selmon->seltags] ^ (arg->ui & TAGMASK);

  if(newtagset) {
    selmon->tagset[selmon->seltags] = newtagset;
    arrange(selmon);
  }
}

void
unfocus(Client *c) {
  if(!c)
    return;
  grabbuttons(c, False);
  XSetWindowBorder(dpy, c->win, dc.norm[ColBorder]);
  XSetInputFocus(dpy, root, RevertToPointerRoot, CurrentTime);
}

void
unmanage(Client *c, Bool destroyed) {
  Monitor *m = c->mon;

  /* The server grab construct avoids race conditions. */
  detach(c);
  detachstack(c);
  if(!destroyed) {
    xcb_grab_server(xcb_dpy);
    xcb_configure_window(xcb_dpy, c->win, XCB_CONFIG_WINDOW_BORDER_WIDTH,
			 &(c->oldbw)); /* restore border */
    xcb_ungrab_button(xcb_dpy, AnyButton, c->win, AnyModifier);
    setclientstate(c, WithdrawnState);
    xcb_flush(xcb_dpy);
    xcb_ungrab_server(xcb_dpy);
  }
  free(c);
  focus(NULL);
  arrange(m);
}

void
unmapnotify(xcb_generic_event_t *e) {
  Client *c;
  xcb_unmap_notify_event_t *ev = (xcb_unmap_notify_event_t *)e;

  if((c = wintoclient(ev->window)))
    unmanage(c, False);
}

void
updatebars(void) {
  Monitor *m;
  uint32_t wa[3];

  wa[1] = 1;
  wa[0] = XCB_BACK_PIXMAP_PARENT_RELATIVE;
  wa[2] = XCB_EVENT_MASK_BUTTON_PRESS | XCB_EVENT_MASK_EXPOSURE;
  for(m = mons; m; m = m->next) {
    m->barwin = xcb_generate_id(xcb_dpy);
    xcb_create_window(xcb_dpy, screen->root_depth, m->barwin,
		      root, m->wx, m->by, m->ww, bh, 0,
		      XCB_WINDOW_CLASS_INPUT_OUTPUT, screen->root_visual,
		      XCB_CW_BACK_PIXMAP | XCB_CW_OVERRIDE_REDIRECT | XCB_CW_EVENT_MASK,
		      wa);
    uint32_t value_list = cursor[CurNormal];
    xcb_change_window_attributes(xcb_dpy, m->barwin, XCB_CW_CURSOR, &value_list);
    xcb_map_window(xcb_dpy, m->barwin);
    xcb_raise_window(xcb_dpy, m->barwin);
  }

  xcb_flush(xcb_dpy);
}

void
updatebarpos(Monitor *m) {
  m->wy = m->my;
  m->wh = m->mh;
  if(m->showbar) {
    m->wh -= bh;
    m->by = m->topbar ? m->wy : m->wy + m->wh;
    m->wy = m->topbar ? m->wy + bh : m->wy;
  }
  else
    m->by = -bh;
}

Bool
updategeom(void) {
  Bool dirty = False;

#ifdef XINERAMA
  if(XineramaIsActive(dpy)) {
    int i, j, n, nn;
    Client *c;
    Monitor *m;
    XineramaScreenInfo *info = XineramaQueryScreens(dpy, &nn);
    XineramaScreenInfo *unique = NULL;

    info = XineramaQueryScreens(dpy, &nn);
    for(n = 0, m = mons; m; m = m->next, n++);
    /* only consider unique geometries as separate screens */
    if(!(unique = (XineramaScreenInfo *)malloc(sizeof(XineramaScreenInfo) * nn)))
      die("fatal: could not malloc() %u bytes\n", sizeof(XineramaScreenInfo) * nn);
    for(i = 0, j = 0; i < nn; i++)
      if(isuniquegeom(unique, j, &info[i]))
	memcpy(&unique[j++], &info[i], sizeof(XineramaScreenInfo));
    XFree(info);
    nn = j;
    if(n <= nn) {
      for(i = 0; i < (nn - n); i++) { /* new monitors available */
	for(m = mons; m && m->next; m = m->next);
	if(m)
	  m->next = createmon();
	else
	  mons = createmon();
      }
      for(i = 0, m = mons; i < nn && m; m = m->next, i++)
	if(i >= n
	   || (unique[i].x_org != m->mx || unique[i].y_org != m->my
	       || unique[i].width != m->mw || unique[i].height != m->mh))
	  {
	    dirty = True;
	    m->num = i;
	    m->mx = m->wx = unique[i].x_org;
	    m->my = m->wy = unique[i].y_org;
	    m->mw = m->ww = unique[i].width;
	    m->mh = m->wh = unique[i].height;
	    updatebarpos(m);
	  }
    }
    else { /* less monitors available nn < n */
      for(i = nn; i < n; i++) {
	for(m = mons; m && m->next; m = m->next);
	while(m->clients) {
	  dirty = True;
	  c = m->clients;
	  m->clients = c->next;
	  detachstack(c);
	  c->mon = mons;
	  attach(c);
	  attachstack(c);
	}
	if(m == selmon)
	  selmon = mons;
	cleanupmon(m);
      }
    }
    free(unique);
  }
  else
#endif /* XINERAMA */
    /* default monitor setup */
    {
      if(!mons)
	mons = createmon();
      if(mons->mw != sw || mons->mh != sh) {
	dirty = True;
	mons->mw = mons->ww = sw;
	mons->mh = mons->wh = sh;
	updatebarpos(mons);
      }
    }
  if(dirty) {
    selmon = mons;
    selmon = wintomon(root);
  }
  return dirty;
}

void
updatenumlockmask(void) {
  unsigned int i, j;
  XModifierKeymap *modmap;

  numlockmask = 0;
  modmap = XGetModifierMapping(dpy);
  for(i = 0; i < 8; i++)
    for(j = 0; j < modmap->max_keypermod; j++)
      if(modmap->modifiermap[i * modmap->max_keypermod + j]
	 == XKeysymToKeycode(dpy, XK_Num_Lock))
	numlockmask = (1 << i);
  XFreeModifiermap(modmap);
}

void
updatesizehints(Client *c) {
  long msize;
  XSizeHints size;

  if(!XGetWMNormalHints(dpy, c->win, &size, &msize))
    /* size is uninitialized, ensure that size.flags aren't used */
    size.flags = PSize;
  if(size.flags & PBaseSize) {
    c->basew = size.base_width;
    c->baseh = size.base_height;
  }
  else if(size.flags & PMinSize) {
    c->basew = size.min_width;
    c->baseh = size.min_height;
  }
  else
    c->basew = c->baseh = 0;
  if(size.flags & PResizeInc) {
    c->incw = size.width_inc;
    c->inch = size.height_inc;
  }
  else
    c->incw = c->inch = 0;
  if(size.flags & PMaxSize) {
    c->maxw = size.max_width;
    c->maxh = size.max_height;
  }
  else
    c->maxw = c->maxh = 0;
  if(size.flags & PMinSize) {
    c->minw = size.min_width;
    c->minh = size.min_height;
  }
  else if(size.flags & PBaseSize) {
    c->minw = size.base_width;
    c->minh = size.base_height;
  }
  else
    c->minw = c->minh = 0;
  if(size.flags & PAspect) {
    c->mina = (float)size.min_aspect.y / size.min_aspect.x;
    c->maxa = (float)size.max_aspect.x / size.max_aspect.y;
  }
  else
    c->maxa = c->mina = 0.0;
  c->isfixed = (c->maxw && c->minw && c->maxh && c->minh
		&& c->maxw == c->minw && c->maxh == c->minh);
}

void
updatetitle(Client *c) {
  if(!gettextprop(c->win, netatom[NetWMName], c->name, sizeof c->name))
    gettextprop(c->win, XA_WM_NAME, c->name, sizeof c->name);
  if(c->name[0] == '\0') /* hack to mark broken clients */
    strcpy(c->name, broken);
}

void
updatestatus(void) {
  if(!gettextprop(root, XA_WM_NAME, stext, sizeof(stext)))
    strcpy(stext, "dwm-"VERSION);
  drawbar(selmon);
}

void
updatewmhints(Client *c) {
  XWMHints *wmh;

  if((wmh = XGetWMHints(dpy, c->win))) {
    if(c == selmon->sel && wmh->flags & XUrgencyHint) {
      wmh->flags &= ~XUrgencyHint;
      XSetWMHints(dpy, c->win, wmh);
    }
    else
      c->isurgent = (wmh->flags & XUrgencyHint) ? True : False;
    XFree(wmh);
  }
}

void
view(const Arg *arg) {
  if((arg->ui & TAGMASK) == selmon->tagset[selmon->seltags])
    return;
  selmon->seltags ^= 1; /* toggle sel tagset */
  if(arg->ui & TAGMASK)
    selmon->tagset[selmon->seltags] = arg->ui & TAGMASK;
  arrange(selmon);
}

void
viewprev(const Arg *arg) {
  unsigned int currentset = selmon->tagset[selmon->seltags];
  currentset = currentset | ((currentset & 1) << LENGTH(tags));
  selmon->seltags ^= 1;
  selmon->tagset[selmon->seltags] = currentset >> 1;
  arrange(selmon);
}

void
viewnext(const Arg *arg) {
  unsigned int currentset = selmon->tagset[selmon->seltags];
  currentset <<= 1;
  currentset |= (currentset & (1LL << LENGTH(tags))) >> LENGTH(tags);
  selmon->seltags ^= 1;
  selmon->tagset[selmon->seltags] = currentset;
  arrange(selmon);
}

Client *
wintoclient(Window w) {
  Client *c;
  Monitor *m;

  for(m = mons; m; m = m->next)
    for(c = m->clients; c; c = c->next)
      if(c->win == w)
	return c;
  return NULL;
}

Monitor *
wintomon(Window w) {
  int x, y;
  Client *c;
  Monitor *m;

  if(w == root && getrootptr(&x, &y))
    return ptrtomon(x, y);
  for(m = mons; m; m = m->next)
    if(w == m->barwin)
      return m;
  if((c = wintoclient(w)))
    return c->mon;
  return selmon;
}

/* There's no way to check accesses to destroyed windows, thus those cases are
 * ignored (especially on UnmapNotify's).  Other types of errors call Xlibs
 * default error handler, which may call exit.  */
int
xerror(Display *dpy, XErrorEvent *ee) {
  if(ee->error_code == BadWindow
     || (ee->request_code == X_SetInputFocus && ee->error_code == BadMatch)
     || (ee->request_code == X_PolyText8 && ee->error_code == BadDrawable)
     || (ee->request_code == X_PolyFillRectangle && ee->error_code == BadDrawable)
     || (ee->request_code == X_PolySegment && ee->error_code == BadDrawable)
     || (ee->request_code == X_ConfigureWindow && ee->error_code == BadMatch)
     || (ee->request_code == X_GrabButton && ee->error_code == BadAccess)
     || (ee->request_code == X_GrabKey && ee->error_code == BadAccess)
     || (ee->request_code == X_CopyArea && ee->error_code == BadDrawable))
    return 0;
  fprintf(stderr, "dwm: fatal error: request code=%d, error code=%d\n",
	  ee->request_code, ee->error_code);
  return xerrorxlib(dpy, ee); /* may call exit */
}

int
xerrordummy(Display *dpy, XErrorEvent *ee) {
  return 0;
}

void
zoom(const Arg *arg) {
  Client *c = selmon->sel;

  if(!selmon->lt[selmon->sellt]->arrange
     || selmon->lt[selmon->sellt]->arrange == monocle
     || (selmon->sel && selmon->sel->isfloating))
    return;
  if(c == nexttiled(selmon->clients))
    if(!c || !(c = nexttiled(c->next)))
      return;
  detach(c);
  attach(c);
  focus(c);
  arrange(c->mon);
}

int
main(int argc, char *argv[]) {
  if(argc == 2 && !strcmp("-v", argv[1]))
    die("dwm-"VERSION", © 2006-2009 dwm engineers, see LICENSE for details\n");
  else if(argc != 1)
    die("usage: dwm [-v]\n");
  if(!setlocale(LC_CTYPE, "") || !XSupportsLocale())
    fputs("warning: no locale support\n", stderr);
  if(!(dpy = XOpenDisplay(NULL)))
    die("dwm: cannot open display\n");
  if(!(xcb_dpy = xcb_connect(NULL,0)))
    die("dwm: cannot open XCB connection to display\n");
  setup();
  scan();
  run();
  cleanup();
  XCloseDisplay(dpy);
  xcb_disconnect(xcb_dpy);
  return 0;
}
