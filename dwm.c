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
#include <assert.h>
#include <errno.h>
#include <locale.h>
#include <stdarg.h>
#include <signal.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <math.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <X11/cursorfont.h>
#include <X11/keysym.h>
// #include <X11/Xlib.h>
#ifdef XINERAMA
#include <xcb/xinerama.h>
#endif /* XINERAMA */

#include <xcb/xcb.h>
#include <xcb/xcb_event.h>
#include <xcb/xcb_icccm.h>
#include <xcb/xcb_keysyms.h>

/* macros */
#define BUTTONMASK              (XCB_EVENT_MASK_BUTTON_PRESS|XCB_EVENT_MASK_BUTTON_RELEASE)
#define CLEANMASK(mask)         (mask & ~(XCB_MOD_MASK_LOCK|numlockmask))
#define INRECT(X,Y,RX,RY,RW,RH) ((X) >= (RX) && (X) < (RX) + (RW) && (Y) >= (RY) && (Y) < (RY) + (RH))
#define ISVISIBLE(C)            ((C->tags & C->mon->tagset[C->mon->seltags]))
#define LENGTH(X)               (sizeof X / sizeof X[0])
#define MAX(A, B)               ((A) > (B) ? (A) : (B))
#define MIN(A, B)               ((A) < (B) ? (A) : (B))
#define MOUSEMASK               (BUTTONMASK|XCB_EVENT_MASK_POINTER_MOTION)
#define WIDTH(X)                ((X)->w + 2 * (X)->bw)
#define HEIGHT(X)               ((X)->h + 2 * (X)->bw)
#define TAGMASK                 ((1 << LENGTH(tags)) - 1)
#define TEXTW(X)                (textnw(X, strlen(X)) + dc.font.height)

#define true 1
#define false 0

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
  int16_t x, y;
  uint16_t w, h;
  int32_t basew, baseh, incw, inch, maxw, maxh, minw, minh;
  uint16_t bw;
  uint32_t oldbw;
  unsigned int tags;
  int isfixed, isfloating, isurgent;
  Client *next;
  Client *snext;
  Monitor *mon;
  xcb_window_t win;
};

typedef struct {
  int16_t x, y;
  uint16_t w, h;
  uint32_t norm[ColLast];
  uint32_t sel[ColLast];
  xcb_drawable_t drawable;
  xcb_gcontext_t gc;
  struct {
    uint16_t ascent;
    uint16_t descent;
    uint16_t height;
    // XFontSet set;
    xcb_font_t xfont;
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
  int16_t by;               /* bar geometry */
  int16_t mx, my, mw, mh;   /* screen size */
  int16_t wx, wy, ww, wh;   /* window area  */
  unsigned int seltags;
  unsigned int sellt;
  unsigned int tagset[2];
  int showbar;
  int topbar;
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
  int isfloating;
  int monitor;
} Rule;

/* function declarations */
static void applyrules(Client *c);
static int applysizehints(Client *c, int16_t *x, int16_t *y, uint16_t *w, uint16_t *h, int interact);
static void arrange(Monitor *m);
static void arrangemon(Monitor *m);
static void attach(Client *c);
static void attachstack(Client *c);
static int buttonpress(void *dummy, xcb_connection_t *dpy, xcb_button_press_event_t *e);
static void checkotherwm(void);
static void cleanup(void);
static void cleanupmon(Monitor *mon);
static void clearurgent(Client *c);
static void configure(Client *c);
static int configurenotify(void *dummy, xcb_connection_t *dpy, xcb_configure_notify_event_t *e);
static int configurerequest(void *dummy, xcb_connection_t *dpy, xcb_configure_request_event_t *e);
static Monitor *createmon(void);
static int destroynotify(void *dummy, xcb_connection_t *dpy, xcb_destroy_notify_event_t *e);
static void detach(Client *c);
static void detachstack(Client *c);
static void die(const char *errstr, ...);
static Monitor *dirtomon(int dir);
static void drawbar(Monitor *m);
static void drawbars(void);
static void drawsquare(int filled, int empty, int invert, uint32_t col[ColLast]);
static void drawtext(const char *text, uint32_t col[ColLast], int invert);
static int enternotify(void *dummy, xcb_connection_t *dpy, xcb_enter_notify_event_t *e);
static int expose(void *dummy, xcb_connection_t *dpy, xcb_expose_event_t *e);
static void focus(Client *c);
static int focusin(void *dummy, xcb_connection_t *dpy, xcb_focus_in_event_t *e);
static void focusmon(const Arg *arg);
static void focusstack(const Arg *arg);
static uint32_t getcolor(const uint16_t rgb[]);
static int getrootptr(int16_t *x, int16_t *y);
// static long getstate(Window w);
static int gettextprop(xcb_window_t w, xcb_atom_t atom, char *text, unsigned int size);
static void grabbuttons(Client *c, int focused);
static void grabkeys(void);
static void initfont(const char *fontstr);
static int isprotodel(Client *c);
static int keypress(void *dummy, xcb_connection_t *dpy, xcb_key_press_event_t *e);
static void killclient(const Arg *arg);
static void manage(xcb_window_t w, xcb_get_window_attributes_reply_t *wa,
		   xcb_get_geometry_cookie_t cookie_g);
static int mappingnotify(void *dummy, xcb_connection_t *dpy, xcb_mapping_notify_event_t *e);
static int maprequest(void *dummy, xcb_connection_t *dpy, xcb_map_request_event_t *e);
static void monocle(Monitor *m);
static void movemouse(const Arg *arg);
static Client *nexttiled(Client *c);
static Monitor *ptrtomon(int x, int y);
static int propertynotify(void *dummy, xcb_connection_t *dpy, xcb_property_notify_event_t *e);
static void quit(const Arg *arg);
static void resize(Client *c, int16_t x, int16_t y, uint16_t w, uint16_t h, int interact);
static void resizemouse(const Arg *arg);
static void restack(Monitor *m);
static void run(void);
static void scan(void);
static void sendmon(Client *c, Monitor *m);
static void setclientstate(Client *c, xcb_wm_state_t state);
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
static void unmanage(Client *c, int destroyed);
static int unmapnotify(void *dummy, xcb_connection_t *dpy, xcb_unmap_notify_event_t *e);
static int updategeom(void);
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
static Client *wintoclient(xcb_window_t w);
static Monitor *wintomon(xcb_window_t w);
static int xerror(void *dummy, xcb_connection_t *dpy, xcb_generic_error_t *ee);
static int xerrordummy(void *dummy, xcb_connection_t *dpy, xcb_generic_error_t *ee);
static void xcb_error_print(void);
static void zoom(const Arg *arg);

/* variables */
static const char broken[] = "broken";
static char stext[256];
static xcb_screen_t *screen;  /* X display screen structure */
/* X display screen geometry width, height */
#define sw (screen->width_in_pixels)
#define sh (screen->height_in_pixels)
static uint16_t bh, blw = 0;      /* bar geometry */
// static int (*xerrorxlib)(Display *, XErrorEvent *);
static uint16_t numlockmask = 0;
static xcb_event_handlers_t evenths;
static xcb_key_symbols_t *keysyms = 0;
static xcb_atom_t wmatom[WMLast], netatom[NetLast];
static int running = true;
static xcb_cursor_t cursor[CurLast];
// static Display *dpy;
static xcb_connection_t *xcb_dpy;
static xcb_generic_error_t *xerr;
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

  cookie = xcb_get_wm_class(xcb_dpy, c->win);
  int ok = xcb_get_wm_class_reply(xcb_dpy, cookie, &ch, &xerr);
  if (!ok) {
    if (xerr) xcb_error_print();
  }
  else {
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
    xcb_get_wm_class_reply_wipe(&ch);
  }

  c->tags = c->tags & TAGMASK ? c->tags & TAGMASK : c->mon->tagset[c->mon->seltags];
}

int
applysizehints(Client *c, int16_t *x, int16_t *y, uint16_t *w, uint16_t *h, int interact) {
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
    int baseismin = c->basew == c->minw && c->baseh == c->minh;
    if(!baseismin) { /* temporarily remove base dimensions */
      *w -= c->basew;
      *h -= c->baseh;
    }
    /* adjust for aspect limits */
    if(c->mina > 0 && c->maxa > 0) {
      if(c->maxa < (float)*w / *h)
	*w = lroundf(*h * c->maxa);
      else if(c->mina < (float)*h / *w)
	*h = lroundf(*w * c->mina);
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

int
buttonpress(void *dummy, xcb_connection_t *dpy, xcb_button_press_event_t *ev) {
  unsigned int i, x, click;
  Arg arg = {0};
  Client *c;
  Monitor *m;

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
  return 1;
}

void
checkotherwm(void) {
  /* this causes an error if some other window manager is running */
  uint32_t mask = XCB_EVENT_MASK_SUBSTRUCTURE_REDIRECT;
  xcb_void_cookie_t cookie = xcb_change_window_attributes_checked
    (xcb_dpy, root, XCB_CW_EVENT_MASK, &mask);
  xerr = xcb_request_check(xcb_dpy, cookie);
  if(xerr)
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
      unmanage(m->stack, false);
  /*  if(dc.font.set)
    XFreeFontSet(dpy, dc.font.set);
    else */
  xcb_close_font(xcb_dpy, dc.font.xfont);
  xcb_ungrab_key(xcb_dpy, XCB_GRAB_ANY, root, XCB_MOD_MASK_ANY);
  xcb_key_symbols_free(keysyms);
  xcb_free_pixmap(xcb_dpy, dc.drawable);
  xcb_free_gc(xcb_dpy, dc.gc);
  xcb_free_cursor(xcb_dpy, cursor[CurNormal]);
  xcb_free_cursor(xcb_dpy, cursor[CurResize]);
  xcb_free_cursor(xcb_dpy, cursor[CurMove]);
  while(mons)
    cleanupmon(mons);
  xcb_flush(xcb_dpy);
  xcb_set_input_focus(xcb_dpy, XCB_INPUT_FOCUS_POINTER_ROOT,
		      XCB_INPUT_FOCUS_POINTER_ROOT, XCB_TIME_CURRENT_TIME);

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

  c->isurgent = false;
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
  xcb_configure_notify_event_t ce;

  ce.response_type = XCB_CONFIGURE_NOTIFY;
  ce.event = c->win;
  ce.window = c->win;
  ce.x = c->x;
  ce.y = c->y;
  ce.width = c->w;
  ce.height = c->h;
  ce.border_width = c->bw;
  ce.above_sibling = XCB_WINDOW_NONE;
  ce.override_redirect = false;
  xcb_send_event(xcb_dpy, 0, c->win, XCB_EVENT_MASK_STRUCTURE_NOTIFY, (const char*)&ce);
}

int
configurenotify(void *dummy, xcb_connection_t *Xdpy, xcb_configure_notify_event_t *ev) {
  Monitor *m;

  if(ev->window == root) {
    sw = ev->width;
    sh = ev->height;
    if(updategeom()) {
      if(dc.drawable != 0)
	xcb_free_pixmap(xcb_dpy, dc.drawable);
      dc.drawable = xcb_generate_id(xcb_dpy);
      xcb_create_pixmap(xcb_dpy, screen->root_depth, dc.drawable, root, sw, bh);
      updatebars();
      for(m = mons; m; m = m->next) {
	uint32_t geometry[] = {m->wx, m->by, m->ww, bh};
	xcb_configure_window(xcb_dpy, m->barwin, XCB_CONFIG_MOVERESIZE, geometry);
      }
      arrange(NULL);
    }
  }

  return 1;
}

int
configurerequest(void *dummy, xcb_connection_t *dpy, xcb_configure_request_event_t *ev) {
  Client *c;
  Monitor *m;

  if((c = wintoclient(ev->window))) {
    if(ev->value_mask & XCB_CONFIG_WINDOW_BORDER_WIDTH)
      c->bw = ev->border_width;
    else if(c->isfloating || !selmon->lt[selmon->sellt]->arrange) {
      m = c->mon;
      if(ev->value_mask & XCB_CONFIG_WINDOW_X)
	c->x = m->mx + ev->x;
      if(ev->value_mask & XCB_CONFIG_WINDOW_Y)
	c->y = m->my + ev->y;
      if(ev->value_mask & XCB_CONFIG_WINDOW_WIDTH)
	c->w = ev->width;
      if(ev->value_mask & XCB_CONFIG_WINDOW_HEIGHT)
	c->h = ev->height;
      if((c->x + c->w) > m->mx + m->mw && c->isfloating)
	c->x = m->mx + (m->mw / 2 - c->w / 2); /* center in x direction */
      if((c->y + c->h) > m->my + m->mh && c->isfloating)
	c->y = m->my + (m->mh / 2 - c->h / 2); /* center in y direction */
      if((ev->value_mask & (XCB_CONFIG_WINDOW_X|XCB_CONFIG_WINDOW_Y))
	 && !(ev->value_mask & (XCB_CONFIG_WINDOW_WIDTH|XCB_CONFIG_WINDOW_HEIGHT)))
	configure(c);
      if(ISVISIBLE(c)) {
	uint32_t geom[] = { c->x, c->y, c->w, c->h };
	xcb_configure_window(xcb_dpy, c->win, XCB_CONFIG_MOVERESIZE, geom);
      }
    }
    else
      configure(c);
  }
  else {
    uint32_t wc[] =
      { ev->x, ev->y, ev->width, ev->height,
	ev->border_width, ev->sibling, ev->stack_mode };
    xcb_configure_window(xcb_dpy, ev->window, ev->value_mask, wc);
  }
  xcb_flush(xcb_dpy);
  return 1;
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

int
destroynotify(void *dummy, xcb_connection_t *dpy, xcb_destroy_notify_event_t *ev) {
  Client *c;
  if((c = wintoclient(ev->window)))
    unmanage(c, true);
  return 1;
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
  int16_t x;
  unsigned int i, occ = 0, urg = 0;
  uint32_t *col;
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
  drawtext(m->ltsymbol, dc.norm, false);
  dc.x += dc.w;
  x = dc.x;
  if(m == selmon) { /* status is only drawn on selected monitor */
    dc.w = TEXTW(stext);
    dc.x = m->ww - dc.w;
    if(dc.x < x) {
      dc.x = x;
      dc.w = m->ww - x;
    }
    drawtext(stext, dc.norm, false);
  }
  else
    dc.x = m->ww;
  if((dc.w = dc.x - x) > bh) {
    dc.x = x;
    if(m->sel) {
      col = m == selmon ? dc.sel : dc.norm;
      drawtext(m->sel->name, col, false);
      drawsquare(m->sel->isfixed, m->sel->isfloating, false, col);
    }
    else
      drawtext(NULL, dc.norm, false);
  }
  xcb_copy_area(xcb_dpy, dc.drawable, m->barwin, dc.gc,
		0, 0, 0, 0, m->ww, bh);
  xcb_flush(xcb_dpy);
}

void
drawbars(void) {
  Monitor *m;

  for(m = mons; m; m = m->next)
    drawbar(m);
}

void
drawsquare(int filled, int empty, int invert, uint32_t col[ColLast]) {
  int16_t x;
  uint32_t gcv;
  xcb_rectangle_t r = { dc.x, dc.y, dc.w, dc.h };

  gcv = col[invert ? ColBG : ColFG];
  xcb_change_gc(xcb_dpy, dc.gc, XCB_GC_FOREGROUND, &gcv);
  x = (dc.font.ascent + dc.font.descent + 2) / 4;
  r.x = dc.x + 1;
  r.y = dc.y + 1;
  if(filled) {
    r.width = r.height = x + 1;
    xcb_poly_fill_rectangle(xcb_dpy, dc.drawable, dc.gc, 1, &r);
  }
  else if(empty) {
    r.width = r.height = x;
    xcb_poly_rectangle(xcb_dpy, dc.drawable, dc.gc, 1, &r);
  }
}

void
drawtext(const char *text, uint32_t col[ColLast], int invert) {
  char buf[256];
  int i;
  int16_t x, y;
  uint16_t h; int len, olen;
  xcb_rectangle_t r = { dc.x, dc.y, dc.w, dc.h };

  uint32_t fg = col[invert ? ColFG : ColBG];
  xcb_change_gc(xcb_dpy, dc.gc, XCB_GC_FOREGROUND, &fg);
  xcb_poly_fill_rectangle(xcb_dpy, dc.drawable, dc.gc, 1, &r);
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
  uint32_t textcol[] = { col[invert ? ColBG : ColFG] ,
			 col[invert ? ColFG : ColBG] };
  xcb_change_gc(xcb_dpy, dc.gc, XCB_GC_FOREGROUND | XCB_GC_BACKGROUND, textcol);
  //  if(dc.font.set)
  //  XmbDrawString(dpy, dc.drawable, dc.font.set, dc.gc_xlib, x, y, buf, len);
  //else
  xcb_image_text_8(xcb_dpy, len, dc.drawable, dc.gc, x, y, buf);
}

int
enternotify(void *dummy, xcb_connection_t *dpy, xcb_enter_notify_event_t *ev) {
  Client *c;
  Monitor *m;

  if((ev->mode != XCB_NOTIFY_MODE_NORMAL
      || ev->detail == XCB_NOTIFY_DETAIL_INFERIOR) && ev->event != root)
    return 0;
  if((m = wintomon(ev->event)) && m != selmon) {
    unfocus(selmon->sel);
    selmon = m;
  }
  if((c = wintoclient(ev->event)))
    focus(c);
  else
    focus(NULL);
  return 1;
}

int
expose(void *dummy, xcb_connection_t *dpy, xcb_expose_event_t *ev) {
  Monitor *m;

  if(ev->count == 0 && (m = wintomon(ev->window)))
    drawbar(m);
  return 1;
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
    grabbuttons(c, true);
    uint32_t border_color[] = { dc.sel[ColBorder] };
    xcb_change_window_attributes(xcb_dpy, c->win, XCB_CW_BORDER_PIXEL, border_color);
    xcb_set_input_focus(xcb_dpy, XCB_INPUT_FOCUS_POINTER_ROOT,
			c->win, XCB_TIME_CURRENT_TIME);
  }
  else
    xcb_set_input_focus(xcb_dpy, XCB_INPUT_FOCUS_POINTER_ROOT,
			root, XCB_TIME_CURRENT_TIME);
  selmon->sel = c;
  drawbars();
}

int
focusin(void *dummy, xcb_connection_t *dpy, xcb_focus_in_event_t *ev) {
  /* there are some broken focus acquiring clients */
  if(selmon->sel && ev->event != selmon->sel->win)
    xcb_set_input_focus(xcb_dpy, XCB_INPUT_FOCUS_POINTER_ROOT,
			selmon->sel->win, XCB_TIME_CURRENT_TIME);
  return 1;
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

uint32_t
getcolor(const uint16_t rgb[]) {
  xcb_colormap_t cmap = screen->default_colormap;
  xcb_alloc_color_cookie_t cookie;
  cookie = xcb_alloc_color(xcb_dpy, cmap, rgb[0], rgb[1], rgb[2]);
  xcb_alloc_color_reply_t *reply =
    xcb_alloc_color_reply(xcb_dpy, cookie, &xerr);

  if(xerr) { xcb_error_print(); exit(1); }
  assert(reply);
  uint32_t result = reply->pixel;
  free(reply);
  return result;
}

int
getrootptr(int16_t *x, int16_t *y) {
  xcb_query_pointer_cookie_t cookie;
  xcb_query_pointer_reply_t *reply;
  cookie = xcb_query_pointer(xcb_dpy, root);
  reply = xcb_query_pointer_reply(xcb_dpy, cookie, &xerr);
  if (xerr) xcb_error_print();
  assert(reply);
  int result = reply->same_screen;
  *x = reply->root_x;
  *y = reply->root_y;
  free(reply);
  return result;
}
/*
long
getstate(Window w) {
  int format, status;
  long result = -1;
  unsigned char *p = NULL;
  unsigned long n, extra;
  Atom real;

  status = XGetWindowProperty(dpy, w, wmatom[WMState], 0L, 2L, false, wmatom[WMState],
			      &real, &format, &n, &extra, (unsigned char **)&p);
  if(status != Success)
    return -1;
  if(n != 0)
    result = *p;
  XFree(p);
  return result;
}
*/
int
gettextprop(xcb_window_t w, xcb_atom_t atom, char *text, unsigned int size) {
  if(!text || size == 0)
    return false;
  text[0] = '\0';

  xcb_get_property_cookie_t cookie;
  xcb_get_text_property_reply_t tp;
  cookie = xcb_get_text_property(xcb_dpy, w, atom);
  int ok = xcb_get_text_property_reply(xcb_dpy, cookie, &tp, &xerr);
  if(!ok) {
    if (xerr) xcb_error_print();
    return false;
  }
  if(!tp.name_len)
    xcb_get_text_property_reply_wipe(&tp);
    return false;
  if(tp.encoding == XCB_ATOM_STRING)
    strncpy(text, tp.name, size - 1);
  /*  else {
  char **list = NULL;
  int n;
    if(XmbTextPropertyToTextList(dpy, &tp, &list, &n) >= Success && n > 0 && *list) {
      strncpy(text, *list, size - 1);
      XFreeStringList(list);
    }
  } */
  text[size - 1] = '\0';
  xcb_get_text_property_reply_wipe(&tp);
  return true;
}

void
grabbuttons(Client *c, int focused) {
  updatenumlockmask();
  {
    unsigned int i, j;
    uint16_t modifiers[] = { 0, XCB_MOD_MASK_LOCK, numlockmask,
			     XCB_MOD_MASK_LOCK | numlockmask };
    xcb_ungrab_button(xcb_dpy, XCB_GRAB_ANY, c->win, XCB_MOD_MASK_ANY);
    if(focused) {
      for(i = 0; i < LENGTH(buttons); i++)
	if(buttons[i].click == ClkClientWin)
	  for(j = 0; j < LENGTH(modifiers); j++)
	    xcb_grab_button(xcb_dpy, 0, c->win,
			    BUTTONMASK, XCB_GRAB_MODE_ASYNC, XCB_GRAB_MODE_ASYNC,
			    XCB_WINDOW_NONE, XCB_CURSOR_NONE,
			    buttons[i].button, buttons[i].mask | modifiers[j]);
    }
    else
      xcb_grab_button(xcb_dpy, 0, c->win,
		      BUTTONMASK, XCB_GRAB_MODE_ASYNC, XCB_GRAB_MODE_ASYNC,
		      XCB_WINDOW_NONE, XCB_CURSOR_NONE,
		      XCB_GRAB_ANY, XCB_BUTTON_MASK_ANY);
  }
}

void
grabkeys(void) {
  updatenumlockmask();
  {
    unsigned int i, j;
    uint16_t modifiers[] = { 0, XCB_MOD_MASK_LOCK, numlockmask,
				 numlockmask | XCB_MOD_MASK_LOCK };
    xcb_keycode_t *code;

    xcb_ungrab_key(xcb_dpy, XCB_GRAB_ANY, root, XCB_MOD_MASK_ANY);
    for(i = 0; i < LENGTH(keys); i++) {
      if((code = xcb_key_symbols_get_keycode(keysyms, keys[i].keysym)))
	{
	  for(j = 0; j < LENGTH(modifiers); j++)
	    xcb_grab_key(xcb_dpy, true, root,
			 keys[i].mod | modifiers[j], code[0],
			 XCB_GRAB_MODE_ASYNC, XCB_GRAB_MODE_ASYNC);
	  free(code);
	}
    }
  }
}

void
initfont(const char *fontstr) {
  char *def, **missing;
  int i, n;

  missing = NULL;
  /*  dc.font.set = XCreateFontSet(dpy, fontstr, &missing, &n, &def);
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
  else { */
    xcb_generic_error_t *error;
    xcb_void_cookie_t cookie;
    xcb_list_fonts_with_info_cookie_t cookie_lf;
    dc.font.xfont = xcb_generate_id(xcb_dpy);
    cookie = xcb_open_font_checked(xcb_dpy, dc.font.xfont, strlen(fontstr), fontstr);
    cookie_lf = xcb_list_fonts_with_info(xcb_dpy, 1, strlen(fontstr), fontstr);
    error = xcb_request_check(xcb_dpy, cookie);
    if(error != NULL) {
      free(error);
      xcb_flush(xcb_dpy);
      cookie = xcb_open_font_checked(xcb_dpy, dc.font.xfont, strlen("fixed"), "fixed");
      cookie_lf = xcb_list_fonts_with_info(xcb_dpy, 1, strlen("fixed"), "fixed");
      error = xcb_request_check(xcb_dpy, cookie);
      if(error != NULL)
	die("error, cannot load font: '%s'\n", fontstr);
    }
    // Get info
    xcb_list_fonts_with_info_reply_t *reply;
    reply = xcb_list_fonts_with_info_reply(xcb_dpy, cookie_lf, NULL);
    if (reply) {
      dc.font.ascent = reply->font_ascent;
      dc.font.descent = reply->font_descent;
    }
    else
      die("could not load font info for '%s'\n", fontstr);
    // }
  dc.font.height = dc.font.ascent + dc.font.descent;
}

int
isprotodel(Client *c) {
  int i;
  int ret = false;

  xcb_get_property_cookie_t cookie;
  cookie = xcb_get_wm_protocols_unchecked(xcb_dpy, c->win, wmatom[WMProtocols]);

  xcb_get_wm_protocols_reply_t protocols;
  if(xcb_get_wm_protocols_reply(xcb_dpy, cookie, &protocols, NULL)) {
    for(i = 0; !ret && i < protocols.atoms_len; i++)
      if(protocols.atoms[i] == wmatom[WMDelete])
	ret = true;
    xcb_get_wm_protocols_reply_wipe(&protocols);
  }
  return ret;
}

#ifdef XINERAMA
static int
isuniquegeom(xcb_xinerama_screen_info_t *unique, size_t len,
	     xcb_xinerama_screen_info_t *info) {
  unsigned int i;

  for(i = 0; i < len; i++)
    if(unique[i].x_org == info->x_org && unique[i].y_org == info->y_org
       && unique[i].width == info->width && unique[i].height == info->height)
      return false;
  return true;
}
#endif /* XINERAMA */

int
keypress(void *dummy, xcb_connection_t *dpy, xcb_key_press_event_t *ev) {
  unsigned int i;
  xcb_keysym_t keysym;

  keysym = xcb_key_symbols_get_keysym(keysyms, ev->detail, 0);
  for(i = 0; i < LENGTH(keys); i++)
    if(keysym == keys[i].keysym
       && CLEANMASK(keys[i].mod) == CLEANMASK(ev->state)
       && keys[i].func)
      keys[i].func(&(keys[i].arg));
  return 1;
}

void
killclient(const Arg *arg) {

  if(!selmon->sel)
    return;
  if(isprotodel(selmon->sel)) {
    xcb_client_message_event_t ev;
    ev.response_type = XCB_CLIENT_MESSAGE;
    ev.format = 32;
    ev.type = wmatom[WMProtocols];
    ev.window = selmon->sel->win;
    ev.data.data32[0] = wmatom[WMDelete];
    ev.data.data32[1] = XCB_CURRENT_TIME;
    xcb_send_event(xcb_dpy, false, selmon->sel->win,
		   XCB_EVENT_MASK_NO_EVENT, (const char *)&ev);
  }
  else {
    int i;
    xcb_grab_server(xcb_dpy);
    for (i = 0; i < 256; ++i)
      xcb_event_set_error_handler(&evenths, i, (xcb_generic_error_handler_t)xerrordummy, NULL);
    xcb_set_close_down_mode(xcb_dpy, XCB_CLOSE_DOWN_DESTROY_ALL);
    xcb_kill_client(xcb_dpy, selmon->sel->win);
    for (i = 0; i < 256; ++i)
      xcb_event_set_error_handler(&evenths, i, (xcb_generic_error_handler_t)xerror, NULL);
    xcb_ungrab_server(xcb_dpy);
  }
  xcb_flush(xcb_dpy);
}

void
manage(xcb_window_t w,
       xcb_get_window_attributes_reply_t *wa,
       xcb_get_geometry_cookie_t cookie_g) {
  static Client cz;
  Client *c, *t = NULL;
  xcb_window_t trans = XCB_WINDOW_NONE;

  if(!(c = malloc(sizeof(Client))))
    die("fatal: could not malloc() %u bytes\n", sizeof(Client));
  *c = cz;
  c->win = w;
  updatetitle(c);

  /* transience */
  xcb_get_property_cookie_t cookie =
    xcb_get_wm_transient_for(xcb_dpy, w);
  xcb_get_wm_transient_for_reply(xcb_dpy, cookie, &trans, &xerr);
  if (xerr) xcb_error_print();
  else t = wintoclient(trans);
  if(t) {
    c->mon = t->mon;
    c->tags = t->tags;
  }
  else {
    c->mon = selmon;
    applyrules(c);
  }

  /* geometry */
  xcb_get_geometry_reply_t *geo = NULL;
  geo = xcb_get_geometry_reply(xcb_dpy, cookie_g, NULL);
  if (!geo) return;

  c->x = geo->x + c->mon->wx;
  c->y = geo->y + c->mon->wy;
  c->w = geo->width;
  c->h = geo->height;
  c->oldbw = geo->border_width;
  free(geo);

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
  uint32_t border_color[] = { dc.norm[ColBorder] };
  xcb_change_window_attributes(xcb_dpy, w, XCB_CW_BORDER_PIXEL, border_color);
  configure(c); /* propagates border_width, if size doesn't change */
  updatesizehints(c);
  uint32_t ev_mask = XCB_EVENT_MASK_ENTER_WINDOW | XCB_EVENT_MASK_FOCUS_CHANGE |
    XCB_EVENT_MASK_PROPERTY_CHANGE | XCB_EVENT_MASK_STRUCTURE_NOTIFY;
  xcb_change_window_attributes(xcb_dpy, w, XCB_CW_EVENT_MASK, &ev_mask);
  grabbuttons(c, false);
  if(!c->isfloating)
    c->isfloating = (trans != XCB_WINDOW_NONE) || c->isfixed;
  if(c->isfloating)
    xcb_raise_window(xcb_dpy, c->win);
  attach(c);
  attachstack(c);

  uint32_t geom[] = {c->x + 2*sw, /* some windows require this */
		     c->y, c->w, c->h };
  xcb_configure_window(xcb_dpy, c->win, XCB_CONFIG_MOVERESIZE, geom);
  xcb_map_window(xcb_dpy, c->win);
  setclientstate(c, XCB_WM_STATE_NORMAL);
  arrange(c->mon);
}

int
mappingnotify(void *dummy, xcb_connection_t *dpy, xcb_mapping_notify_event_t *ev) {
  xcb_refresh_keyboard_mapping(NULL, ev);
  if(ev->request == XCB_MAPPING_KEYBOARD)
    grabkeys();
  return 1;
}

int
maprequest(void *dummy, xcb_connection_t *dpy, xcb_map_request_event_t *ev) {
  static xcb_get_window_attributes_reply_t *wa = NULL;

  xcb_get_window_attributes_cookie_t cookie;
  cookie = xcb_get_window_attributes_unchecked(xcb_dpy, ev->window);
  xcb_get_geometry_cookie_t cookie_g;
  xcb_drawable_t d = { ev->window };
  cookie_g = xcb_get_geometry_unchecked(xcb_dpy, d);

  if(!(wa = xcb_get_window_attributes_reply(xcb_dpy, cookie, NULL)))
    return 0;
  if(wa->override_redirect)
    return 1;
  if(!wintoclient(ev->window))
    manage(ev->window, wa, cookie_g);
  free(wa);
  return 1;
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
    resize(c, m->wx, m->wy, m->ww - 2 * c->bw, m->wh - 2 * c->bw, false);
}

void
movemouse(const Arg *arg) {
  int16_t x, y, ocx, ocy, nx, ny;
  Client *c;
  Monitor *m;
  xcb_generic_event_t *ev = NULL;
  xcb_motion_notify_event_t *e;

  if(!(c = selmon->sel))
    return;
  restack(selmon);
  ocx = c->x;
  ocy = c->y;
  // Grab pointer
  xcb_grab_pointer_cookie_t cookie;
  cookie = xcb_grab_pointer(xcb_dpy, false, root, MOUSEMASK,
			    XCB_GRAB_MODE_ASYNC, XCB_GRAB_MODE_ASYNC,
			    XCB_WINDOW_NONE, cursor[CurMove], XCB_CURRENT_TIME);
  xcb_grab_pointer_reply_t *reply;
  reply = xcb_grab_pointer_reply(xcb_dpy, cookie, &xerr);
  if (xerr) xcb_error_print();
  assert(reply);
  if(reply->status != XCB_GRAB_STATUS_SUCCESS) {
    free(reply);
    return;
  }
  free(reply);

  if(!getrootptr(&x, &y))
    return;
  do {
    // XCB does not provide an alternative to XMaskEvent
    if (ev) free(ev);
    ev = xcb_wait_for_event(xcb_dpy);
    if (!ev) continue;
    switch (ev->response_type) {
    case XCB_CONFIGURE_REQUEST:
    case XCB_EXPOSE:
    case XCB_MAP_REQUEST:
      xcb_event_handle(&evenths, ev);
      break;
    case XCB_MOTION_NOTIFY:
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
	resize(c, nx, ny, c->w, c->h, true);
      break;
    }
  } while(ev->response_type != XCB_BUTTON_RELEASE);
  if (ev) free(ev);
  xcb_ungrab_pointer(xcb_dpy, XCB_CURRENT_TIME);
  xcb_flush(xcb_dpy);
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

int
propertynotify(void *dummy, xcb_connection_t *Xdpy, xcb_property_notify_event_t *ev) {
  Client *c;
  xcb_window_t trans;
  xcb_get_property_cookie_t cookie;

  if((ev->window == root) && (ev->atom == XCB_ATOM_WM_NAME))
    updatestatus();
  else if(ev->state == XCB_PROPERTY_DELETE)
    return 0; /* ignore */
  else if((c = wintoclient(ev->window))) {
    switch (ev->atom) {
    default: break;
    case XCB_ATOM_WM_TRANSIENT_FOR:
      cookie = xcb_get_wm_transient_for_unchecked(xcb_dpy, c->win);
      xcb_get_wm_transient_for_reply(xcb_dpy, cookie, &trans, NULL);
      if(!c->isfloating && (c->isfloating = (wintoclient(trans) != NULL)))
	arrange(c->mon);
      break;
    case XCB_ATOM_WM_NORMAL_HINTS:
      updatesizehints(c);
      break;
    case XCB_ATOM_WM_HINTS:
      updatewmhints(c);
      drawbars();
      break;
    }
    if(ev->atom == XCB_ATOM_WM_NAME || ev->atom == netatom[NetWMName]) {
      updatetitle(c);
      if(c == c->mon->sel)
	drawbar(c->mon);
    }
  }

  return 1;
}

void
quit(const Arg *arg) {
  running = false;
}

void
resize(Client *c, int16_t x, int16_t y, uint16_t w, uint16_t h, int interact) {
  if(applysizehints(c, &x, &y, &w, &h, interact)) {
    c->x = x; c->y = y; c->w = w; c->h = h;
    uint32_t geom[] = {x, y, w, h, c->bw};
    xcb_configure_window(xcb_dpy, c->win, XCB_CONFIG_MOVERESIZE |
			 XCB_CONFIG_WINDOW_BORDER_WIDTH, geom);
    configure(c);
    xcb_flush(xcb_dpy);
  }
}

void
resizemouse(const Arg *arg) {
  int16_t ocx, ocy;
  uint16_t nw, nh;
  Client *c;
  Monitor *m;
  xcb_generic_event_t *ev = NULL;
  xcb_motion_notify_event_t *e;

  if(!(c = selmon->sel))
    return;
  restack(selmon);
  ocx = c->x;
  ocy = c->y;
  // Grab pointer
  xcb_grab_pointer_cookie_t cookie;
  cookie = xcb_grab_pointer(xcb_dpy, false, root, MOUSEMASK,
			    XCB_GRAB_MODE_ASYNC, XCB_GRAB_MODE_ASYNC,
			    XCB_WINDOW_NONE, cursor[CurResize], XCB_CURRENT_TIME);
  xcb_grab_pointer_reply_t *reply;
  reply = xcb_grab_pointer_reply(xcb_dpy, cookie, &xerr);
  if (xerr) xcb_error_print();
  assert(reply);
  if(reply->status != XCB_GRAB_STATUS_SUCCESS) {
    free(reply);
    return;
  }
  free(reply);

  xcb_warp_pointer(xcb_dpy, XCB_NONE, c->win, 0, 0, 0, 0,
		   c->w + c->bw - 1, c->h + c->bw - 1);
  do {
    // XCB does not provide an equivalent for XMaskEvent
    if (ev) free(ev);
    ev = xcb_wait_for_event(xcb_dpy);
    switch(ev->response_type) {
    case XCB_CONFIGURE_REQUEST:
    case XCB_EXPOSE:
    case XCB_MAP_REQUEST:
      xcb_event_handle(&evenths, ev);
      break;
    case XCB_MOTION_NOTIFY:
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
	resize(c, c->x, c->y, nw, nh, true);
      break;
    }
  } while(ev->response_type != XCB_BUTTON_RELEASE);
  if(ev) free(ev);
  xcb_warp_pointer(xcb_dpy, XCB_NONE, c->win, 0, 0, 0, 0, c->w + c->bw - 1, c->h + c->bw - 1);
  xcb_ungrab_pointer(xcb_dpy, XCB_CURRENT_TIME);
  xcb_flush(xcb_dpy);
  // while(XCheckMaskEvent(dpy, EnterWindowMask, &xev));
  if((m = ptrtomon(c->x + c->w / 2, c->y + c->h / 2)) != selmon) {
    sendmon(c, m);
    selmon = m;
    focus(NULL);
  }
}

void
restack(Monitor *m) {
  Client *c;

  drawbar(m);
  if(!m->sel)
    return;
  if(m->sel->isfloating || !m->lt[m->sellt]->arrange)
    xcb_raise_window(xcb_dpy, m->sel->win);
  if(m->lt[m->sellt]->arrange) {
    uint32_t wc[] = { m->barwin, XCB_STACK_MODE_BELOW };
    for(c = m->stack; c; c = c->snext)
      if(!c->isfloating && ISVISIBLE(c)) {
	xcb_configure_window(xcb_dpy, c->win,
			     XCB_CONFIG_WINDOW_SIBLING | XCB_CONFIG_WINDOW_STACK_MODE,
			     wc);
	wc[0] = c->win;
      }
  }

  xcb_flush(xcb_dpy);

  // while(XCheckMaskEvent(dpy, EnterWindowMask, &ev));
}

void
run(void) {
  xcb_generic_event_t *ev;

  /* main event loop */
  xcb_flush(xcb_dpy);
  while(running && (ev = xcb_wait_for_event(xcb_dpy)))
    {
    xcb_event_handle(&evenths, ev); /* call handler */
    free(ev);
    }
}

void
scan(void) {
  unsigned int i, num;
  xcb_window_t *wins = NULL;

  xcb_query_tree_cookie_t cookie = xcb_query_tree(xcb_dpy, root);
  xcb_query_tree_reply_t *qtree = NULL;
  qtree = xcb_query_tree_reply(xcb_dpy, cookie, &xerr);
  if (xerr) xcb_error_print();
  assert(qtree);
  num = qtree->children_len;
  wins = xcb_query_tree_children(qtree);
  int *is_transient = calloc(num, sizeof(int));

  // Send requests for attributes
  xcb_get_window_attributes_cookie_t *cookie_wa =
    malloc(num * sizeof(xcb_get_window_attributes_cookie_t));
  xcb_get_property_cookie_t *cookie_tr =
    malloc(num * sizeof(xcb_get_property_cookie_t));
  xcb_get_property_cookie_t *cookie_h =
    malloc(num * sizeof(xcb_get_property_cookie_t));
  xcb_get_geometry_cookie_t *cookie_g =
    malloc(num * sizeof(xcb_get_geometry_cookie_t));
  xcb_get_window_attributes_reply_t **wa =
    calloc(num, sizeof(xcb_get_window_attributes_reply_t*));
  for(i=0; i<num; i++) {
    cookie_wa[i] = xcb_get_window_attributes_unchecked(xcb_dpy, wins[i]);
    cookie_tr[i] = xcb_get_wm_transient_for_unchecked(xcb_dpy, wins[i]);
    cookie_h[i] = xcb_get_wm_hints_unchecked(xcb_dpy, wins[i]);
    xcb_drawable_t d = { wins[i] };
    cookie_g[i] = xcb_get_geometry_unchecked(xcb_dpy, d);
  }

  // Go through children
  xcb_wm_hints_t hints;
  for(i=0; i<num; i++) {
    // Get attributes
    wa[i] = xcb_get_window_attributes_reply(xcb_dpy, cookie_wa[i], NULL);
    if (!wa[i]) continue;
    // Check for transience
    xcb_window_t transient_for;
    if(xcb_get_wm_transient_for_reply(xcb_dpy, cookie_tr[i], &transient_for, NULL))
      is_transient[i] = 1;
    // Manage window
    xcb_get_wm_hints_reply(xcb_dpy, cookie_h[i], &hints, NULL);
    if (wa[i]->map_state == XCB_MAP_STATE_VIEWABLE || (hints.initial_state == XCB_WM_STATE_ICONIC))
      {
	if (is_transient[i]) continue; // wa[i] is not freed now
	if (!(wa[i]->override_redirect)) manage(wins[i], wa[i], cookie_g[i]);
      }
    else
      { is_transient[i] = 0; }
    free(wa[i]);
  }

  free(cookie_wa);
  free(cookie_tr);
  free(cookie_h);

  for(i=0; i<num; i++)
    if (is_transient[i]) {
      manage(wins[i], wa[i], cookie_g[i]);
      free(wa[i]);
    }

  free(qtree);
  free(wa);
  free(cookie_g);
  free(is_transient);
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
setclientstate(Client *c, xcb_wm_state_t state) {
  long data[] = { state, XCB_NONE };

  xcb_change_property(xcb_dpy, XCB_PROP_MODE_REPLACE, c->win,
		      wmatom[WMState], wmatom[WMState], 32,
		      2, data);
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
  f = arg->f < 1.0f ? arg->f + selmon->mfact : arg->f - 1.0f;
  if(f < 0.1f || f > 0.9f)
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
  /* init handlers */
  xcb_event_handlers_init(xcb_dpy, &evenths);
  xcb_event_set_button_press_handler(&evenths, buttonpress, NULL);
  xcb_event_set_configure_request_handler(&evenths, configurerequest, NULL);
  xcb_event_set_configure_notify_handler(&evenths, configurenotify, NULL);
  xcb_event_set_destroy_notify_handler(&evenths, destroynotify, NULL);
  xcb_event_set_enter_notify_handler(&evenths, enternotify, NULL);
  xcb_event_set_expose_handler(&evenths, expose, NULL);
  xcb_event_set_focus_in_handler(&evenths, focusin, NULL);
  xcb_event_set_key_press_handler(&evenths, keypress, NULL);
  xcb_event_set_mapping_notify_handler(&evenths, mappingnotify, NULL);
  xcb_event_set_map_request_handler(&evenths, maprequest, NULL);
  xcb_event_set_property_notify_handler(&evenths, propertynotify, NULL);
  xcb_event_set_unmap_notify_handler(&evenths, unmapnotify, NULL);
  /* init error handler */
  int i;
  for (i = 0; i < 256; ++i)
    xcb_event_set_error_handler(&evenths, i, (xcb_generic_error_handler_t)xerror, NULL);
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
  xcb_void_cookie_t cookie_fc =
    xcb_open_font_checked(xcb_dpy, font, strlen("cursor"), "cursor");
  xerr = xcb_request_check(xcb_dpy, cookie_fc);
  if(xerr) {
    xcb_error_print();
    die("dwm: error loading cursor font\n");
  }
  cursor[CurNormal] = xcb_generate_id(xcb_dpy);
  cursor[CurResize] = xcb_generate_id(xcb_dpy);
  cursor[CurMove] = xcb_generate_id(xcb_dpy);
  xcb_create_glyph_cursor(xcb_dpy, cursor[CurNormal], font, font,
			  XC_left_ptr, XC_left_ptr + 1,
			  0, 0, 0, 0xffff, 0xffff, 0xffff);
  xcb_create_glyph_cursor(xcb_dpy, cursor[CurResize], font, font,
			  XC_sizing, XC_sizing + 1,
			  0, 0, 0, 0xffff, 0xffff, 0xffff);
  xcb_create_glyph_cursor(xcb_dpy, cursor[CurMove], font, font,
			  XC_fleur, XC_fleur + 1,
			  0, 0, 0, 0xffff, 0xffff, 0xffff);
  /* init appearance */
  dc.norm[ColBorder] = getcolor(normbordercolor);
  dc.norm[ColBG] = getcolor(normbgcolor);
  dc.norm[ColFG] = getcolor(normfgcolor);
  dc.sel[ColBorder] = getcolor(selbordercolor);
  dc.sel[ColBG] = getcolor(selbgcolor);
  dc.sel[ColFG] = getcolor(selfgcolor);
  dc.drawable = xcb_generate_id(xcb_dpy);
  xcb_create_pixmap(xcb_dpy, screen->root_depth, dc.drawable, root, sw, bh);
  dc.gc = xcb_generate_id(xcb_dpy);
  xcb_create_gc(xcb_dpy, dc.gc, root, 0, NULL);
  uint32_t line_attrs[] = { 1, XCB_LINE_STYLE_SOLID, XCB_CAP_STYLE_BUTT,
			    XCB_JOIN_STYLE_MITER };
  xcb_change_gc(xcb_dpy, dc.gc, XCB_GC_LINE_WIDTH | XCB_GC_LINE_STYLE
		| XCB_GC_CAP_STYLE | XCB_GC_JOIN_STYLE, line_attrs);
  //  if(!dc.font.set)
  xcb_change_gc(xcb_dpy, dc.gc, XCB_GC_FONT, &dc.font.xfont);
  xcb_flush(xcb_dpy);
  /* init bars */
  updatebars();
  updatestatus();
  /* EWMH support per view */
  xcb_change_property(xcb_dpy, XCB_PROP_MODE_REPLACE, root,
		      netatom[NetSupported], XCB_ATOM_ATOM, 32,
		      NetLast, netatom);
  /* select for events */
  uint32_t wa = cursor[CurNormal];
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
      resize(c, c->x, c->y, c->w, c->h, false);
    showhide(c->snext);
  }
  else { /* hide clients bottom up */
    showhide(c->snext);
    geom[0] = c->x + 2 * sw; geom[1] = c->y;
    xcb_configure_window(xcb_dpy, c->win, XCB_CONFIG_WINDOW_X | XCB_CONFIG_WINDOW_Y, geom);
  }
  xcb_flush(xcb_dpy);
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
    if(xcb_dpy)
      close(xcb_get_file_descriptor(xcb_dpy));
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
  /*  if(dc.font.set) {
    XRectangle r;
    XmbTextExtents(dc.font.set, text, len, NULL, &r);
    return r.width;
    } */

  xcb_char2b_t *text2 = (xcb_char2b_t *)calloc(len, sizeof(xcb_char2b_t));
  int i;
  for(i = 0; i < len; i++)
    { text2[i].byte1 = 0; text2[i].byte2 = text[i]; }
  xcb_query_text_extents_cookie_t cookie;
  xcb_query_text_extents_reply_t *reply;
  cookie = xcb_query_text_extents(xcb_dpy, dc.font.xfont, len, text2);
  reply = xcb_query_text_extents_reply(xcb_dpy, cookie, &xerr);
  free(text2);
  if (xerr) xcb_error_print();
  assert(reply);
  int32_t w = reply->overall_width;
  free(reply);
  return(w);
}

void
tile(Monitor *m) {
  int16_t x, y;
  uint16_t h, w, mw;
  unsigned int i, n;
  Client *c;

  for(n = 0, c = nexttiled(m->clients); c; c = nexttiled(c->next), n++);
  if(n == 0)
    return;
  /* master */
  c = nexttiled(m->clients);
  mw = lroundf(m->mfact * m->ww);
  resize(c, m->wx, m->wy, (n == 1 ? m->ww : mw) - 2 * c->bw, m->wh - 2 * c->bw, false);
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
						    ? m->wy + m->wh - y - 2 * c->bw : h - 2 * c->bw), false);
    if(h != m->wh)
      y = c->y + HEIGHT(c);
  }
}

void
togglebar(const Arg *arg) {
  selmon->showbar = !selmon->showbar;
  updatebarpos(selmon);
  uint32_t geom[] = {selmon->wx, selmon->by, selmon->ww, bh};
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
	   selmon->sel->w, selmon->sel->h, false);
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
  grabbuttons(c, false);
  uint32_t border_color[] = { dc.norm[ColBorder] };
  xcb_change_window_attributes(xcb_dpy, c->win, XCB_CW_BORDER_PIXEL, border_color);
  xcb_set_input_focus(xcb_dpy, XCB_INPUT_FOCUS_POINTER_ROOT,
		      root, XCB_TIME_CURRENT_TIME);
}

void
unmanage(Client *c, int destroyed) {
  Monitor *m = c->mon;

  /* The server grab construct avoids race conditions. */
  detach(c);
  detachstack(c);
  if(!destroyed) {
    xcb_grab_server(xcb_dpy);
    xcb_configure_window(xcb_dpy, c->win, XCB_CONFIG_WINDOW_BORDER_WIDTH,
			 &(c->oldbw)); /* restore border */
    xcb_ungrab_button(xcb_dpy, XCB_GRAB_ANY, c->win, XCB_MOD_MASK_ANY);
    setclientstate(c, XCB_WM_STATE_WITHDRAWN);
    xcb_ungrab_server(xcb_dpy);
    xcb_flush(xcb_dpy);
  }
  free(c);
  focus(NULL);
  arrange(m);
}

int
unmapnotify(void *dummy, xcb_connection_t *dpy, xcb_unmap_notify_event_t *ev) {
  Client *c = wintoclient(ev->window);
  if(c) unmanage(c, false);
  return 1;
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
    xcb_cursor_t value_list[] = { cursor[CurNormal] };
    xcb_change_window_attributes(xcb_dpy, m->barwin, XCB_CW_CURSOR, (uint32_t*)value_list);
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

int
updategeom(void) {
  int dirty = false;

#ifdef XINERAMA
  xcb_xinerama_is_active_cookie_t cookie;
  cookie = xcb_xinerama_is_active_unchecked(xcb_dpy);
  xcb_xinerama_is_active_reply_t *xinerama_r;
  xinerama_r = xcb_xinerama_is_active_reply(xcb_dpy, cookie, NULL);
  if(xinerama_r && xinerama_r->state) {
    free(xinerama_r);

    int i, j, n, nn;
    Client *c;
    Monitor *m;
    xcb_xinerama_query_screens_cookie_t cookie;
    xcb_xinerama_query_screens_reply_t *reply_qs;
    xcb_xinerama_screen_info_t *info;
    xcb_xinerama_screen_info_t *unique = NULL;

    size_t sinfo_s = sizeof(xcb_xinerama_screen_info_t);

    cookie = xcb_xinerama_query_screens_unchecked(xcb_dpy);
    reply_qs = xcb_xinerama_query_screens_reply(xcb_dpy, cookie, NULL);
    info = xcb_xinerama_query_screens_screen_info(reply_qs);
    nn = xcb_xinerama_query_screens_screen_info_length(reply_qs);

    for(n = 0, m = mons; m; m = m->next, n++);

    /* only consider unique geometries as separate screens */
    if(!(unique = (xcb_xinerama_screen_info_t *)malloc(sinfo_s * nn)))
      die("fatal: could not malloc() %u bytes\n", sinfo_s * nn);
    for(i = 0, j = 0; i < nn; i++)
      if(isuniquegeom(unique, j, &info[i]))
	memcpy(&unique[j++], &info[i], sinfo_s);
    free(reply_qs);
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
	    dirty = true;
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
	  dirty = true;
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
	dirty = true;
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
  xcb_get_modifier_mapping_cookie_t cookie;
  xcb_get_modifier_mapping_reply_t *reply;

  numlockmask = 0;
  cookie = xcb_get_modifier_mapping(xcb_dpy);
  reply = xcb_get_modifier_mapping_reply(xcb_dpy, cookie, &xerr);
  if (xerr) xcb_error_print();
  assert(reply);
  xcb_keycode_t *modmap = xcb_get_modifier_mapping_keycodes(reply);
  xcb_keycode_t *keylock = xcb_key_symbols_get_keycode(keysyms, XK_Num_Lock);
  for(i = 0; i < 8; i++)
    for(j = 0; j < reply->keycodes_per_modifier; j++)
      if(modmap[i * reply->keycodes_per_modifier + j]
	 == *keylock)
	numlockmask = (1 << i);
  free(keylock);
  free(reply);
}

void
updatesizehints(Client *c) {
  xcb_get_property_cookie_t cookie;
  xcb_size_hints_t size;
  cookie = xcb_get_wm_normal_hints_unchecked(xcb_dpy, c->win);

  if(!xcb_get_wm_normal_hints_reply(xcb_dpy, cookie, &size, NULL))
    /* size is uninitialized, ensure that size.flags aren't used */
    size.flags = XCB_SIZE_HINT_P_SIZE;
  if(size.flags & XCB_SIZE_HINT_BASE_SIZE) {
    c->basew = size.base_width;
    c->baseh = size.base_height;
  }
  else if(size.flags & XCB_SIZE_HINT_P_MIN_SIZE) {
    c->basew = size.min_width;
    c->baseh = size.min_height;
  }
  else
    c->basew = c->baseh = 0;
  if(size.flags & XCB_SIZE_HINT_P_RESIZE_INC) {
    c->incw = size.width_inc;
    c->inch = size.height_inc;
  }
  else
    c->incw = c->inch = 0;
  if(size.flags & XCB_SIZE_HINT_P_MAX_SIZE) {
    c->maxw = size.max_width;
    c->maxh = size.max_height;
  }
  else
    c->maxw = c->maxh = 0;
  if(size.flags & XCB_SIZE_HINT_P_MIN_SIZE) {
    c->minw = size.min_width;
    c->minh = size.min_height;
  }
  else if(size.flags & XCB_SIZE_HINT_BASE_SIZE) {
    c->minw = size.base_width;
    c->minh = size.base_height;
  }
  else
    c->minw = c->minh = 0;
  if(size.flags & XCB_SIZE_HINT_P_ASPECT) {
    c->mina = (float)size.min_aspect_num / size.min_aspect_den;
    c->maxa = (float)size.max_aspect_num / size.max_aspect_den;
  }
  else
    c->maxa = c->mina = 0.0;
  c->isfixed = (c->maxw && c->minw && c->maxh && c->minh
		&& c->maxw == c->minw && c->maxh == c->minh);
}

void
updatetitle(Client *c) {
  if(!gettextprop(c->win, netatom[NetWMName], c->name, sizeof c->name))
    gettextprop(c->win, XCB_ATOM_WM_NAME, c->name, sizeof c->name);
  if(c->name[0] == '\0') /* hack to mark broken clients */
    strcpy(c->name, broken);
}

void
updatestatus(void) {
  if(!gettextprop(root, XCB_ATOM_WM_NAME, stext, sizeof(stext)))
    strcpy(stext, "dwm-"VERSION);
  drawbar(selmon);
}

void
updatewmhints(Client *c) {
  xcb_get_property_cookie_t cookie;
  xcb_wm_hints_t hints;

  cookie = xcb_get_wm_hints(xcb_dpy, c->win);
  xcb_get_wm_hints_reply(xcb_dpy, cookie, &hints, &xerr);
  if (xerr) {
    xcb_error_print(); return; }
  else {
    if(c == selmon->sel && hints.flags & XCB_WM_HINT_X_URGENCY) {
      hints.flags &= ~XCB_WM_HINT_X_URGENCY;
      xcb_set_wm_hints(xcb_dpy, c->win, &hints);
    }
    else
      c->isurgent = (hints.flags & XCB_WM_HINT_X_URGENCY) ? true : false;
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
wintoclient(xcb_window_t w) {
  Client *c;
  Monitor *m;

  for(m = mons; m; m = m->next)
    for(c = m->clients; c; c = c->next)
      if(c->win == w)
	return c;
  return NULL;
}

Monitor *
wintomon(xcb_window_t w) {
  int16_t x, y;
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
xerror(void *dummy, xcb_connection_t *dpy, xcb_generic_error_t *ee) {
  if(ee->error_code == XCB_EVENT_ERROR_BAD_WINDOW
     || (ee->major_code == XCB_SET_INPUT_FOCUS && ee->error_code == XCB_EVENT_ERROR_BAD_MATCH)
     || (ee->major_code == XCB_POLY_TEXT_8 && ee->error_code == XCB_EVENT_ERROR_BAD_DRAWABLE)
     || (ee->major_code == XCB_POLY_FILL_RECTANGLE && ee->error_code == XCB_EVENT_ERROR_BAD_DRAWABLE)
     || (ee->major_code == XCB_POLY_SEGMENT && ee->error_code == XCB_EVENT_ERROR_BAD_DRAWABLE)
     || (ee->major_code == XCB_CONFIGURE_WINDOW && ee->error_code == XCB_EVENT_ERROR_BAD_MATCH)
     || (ee->major_code == XCB_GRAB_BUTTON && ee->error_code == XCB_EVENT_ERROR_BAD_ACCESS)
     || (ee->major_code == XCB_GRAB_KEY && ee->error_code == XCB_EVENT_ERROR_BAD_ACCESS)
     || (ee->major_code == XCB_COPY_AREA && ee->error_code == XCB_EVENT_ERROR_BAD_DRAWABLE))
    return 0;
  fprintf(stderr, "dwm: fatal error: request code=%d (%s), error code=%d (%s)\n",
	  ee->major_code, xcb_event_get_request_label(ee->major_code),
	  ee->error_code, xcb_event_get_error_label(ee->error_code));
  return 1;
  // return xerrorxlib(dpy, ee); /* may call exit */
}

int
xerrordummy(void *dummy, xcb_connection_t *dpy, xcb_generic_error_t *ee) {
  return 0;
}

void
xcb_error_print(void)
{
  if (xerr) {
    fprintf(stderr, "dwm: X error: request %d (%s), error %d (%s)\n",
	    xerr->major_code, xcb_event_get_request_label(xerr->major_code),
	    xerr->error_code, xcb_event_get_error_label(xerr->error_code));
    free(xerr);
  }
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
  if(!setlocale(LC_CTYPE, "")) // || !XSupportsLocale())
    fputs("warning: no locale support\n", stderr);
  // if(!(dpy = XOpenDisplay(NULL)))
  //   die("dwm: cannot open display\n");
  if(!(xcb_dpy = xcb_connect(NULL,0)))
    die("dwm: cannot open XCB connection to display\n");
  setup();
  scan();
  run();
  cleanup();
  // XCloseDisplay(dpy);
  xcb_disconnect(xcb_dpy);
  return 0;
}
