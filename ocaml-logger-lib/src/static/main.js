/**
 * Create a new 'button' element, with a label.
 * @param label - the text label for the button.
 */
function button_with_label(label) {
  var button = document.createElement('button');
  button.appendChild(document.createTextNode(label));
  return button;
}

/**
 * Create a new checkbox element, with a label.
 * @param p - parent element, typically a 'p'.
 * @param label - text label to put next to the checkbox.
 * @param initial_state - should the checkbox be checked initially?
 * @param callback - function to be called with the state on state change.
 */
function add_checkbox(p, label, initial_state, callback) {
  var checkbox = document.createElement('input');
  checkbox.type = "checkbox";
  checkbox.checked = initial_state;
  checkbox.id = label;
  p.appendChild(checkbox);

  var checkbox_label = document.createElement('label')
  checkbox_label.htmlFor = label;
  checkbox_label.appendChild(document.createTextNode(label));
  p.appendChild(checkbox_label);

  callback(initial_state);
  checkbox.onchange = () => callback(checkbox.checked);
}

/**
 * Class representing a "log item", that is, a span or an event.
 */
class LogItem {
  /**
   * @param root - the "div" at the root of the log.
   * @param parent_span - the parent of the item in the log (may be null).
   * @param json - JSON data from which the log item is build.
   */
  constructor(root, parent_span, json) {
    // Recording the initial parameters.
    this.root = root;
    this.parent_span = parent_span;
    this.json = json;

    // The main "div" containing the HTML for the item.
    this.wrapper_div = document.createElement('div');
    this.scroll_to = this.wrapper_div;

    // Boolean indicating whether the element has a search highlight.
    this.is_highlighted = false;

    // Add the element to its parent.
    if(this.parent_span === null) {
      this.root.appendChild(this.wrapper_div);
    } else {
      this.parent_span.append_child(this);
    }
  }

  /**
   * Set the highlighting state of the item (used, e.g., for searches).
   * @param b - should we highlight the element?
   */
  set_highlighted(b) {
    if(this.is_highlighted == b) return;
    this.is_highlighted = b;
    if(this.is_highlighted) {
      this.wrapper_div.classList.add('search_highlight');
    } else {
      this.wrapper_div.classList.remove('search_highlight');
    }
  }

  /**
   * Make sure the item and all its parents are visible, and scroll to the
   * start of the item.
   */
  scroll_into_view() {
    if(this.parent_span !== null) this.parent_span.unfold();
    let config = {behavior: 'smooth', block: 'start', inline: 'nearest'};
    let saved = this.scroll_to.style.scrollMarginTop;
    this.scroll_to.style.scrollMarginTop = '200px';
    this.scroll_to.scrollIntoView(config);
    this.scroll_to.classList.add('scrolled_to');
    let f = () => {
      this.scroll_to.classList.remove('scrolled_to');
      this.scroll_to.style.scrollMarginTop = saved;
    };
    window.setTimeout(f, 2000);
  }
}

/**
 * Class representing a "log event".
 */
class Event extends LogItem {
  /**
   * @param root - the "div" at the root of the log.
   * @param parent_span - the parent of the item in the log (may be null).
   * @param header - a header for the event (may be null).
   * @param json - JSON data from which the log item is build.
   * @param metadata - an association list of metadata.
   */
  constructor(root, parent_span, header, json, metadata) {
    super(root, parent_span, json);
    this.wrapper_div.classList.add('log_event');

    this.text = null;
    this.header_text = null;
    this.metadata = metadata;
    this.tags_p = document.createElement('p');
    this.header_p = null;
    this.data_pre = document.createElement('pre');
    this.large = false;
    this.folded = false;
    this.is_span = false;
    this.is_event = true;

    // Adding metadata.
    this.tags_p.classList.add('log_event_tag');
    this.wrapper_div.appendChild(this.tags_p);

    // Writing the metadata contents.
    var metadata_text = "(metadata: ";
    var first_metadata_item = true;
    for(var k in metadata) {
      var v = metadata[k];
      if(typeof json !== 'string') v = JSON.stringify(v);
      if(first_metadata_item) {
        first_metadata_item = false;
      } else {
        metadata_text += ", ";
      }
      metadata_text += k + "=" + v;
    }
    if(first_metadata_item) metadata_text += "none";
    metadata_text += ")";
    this.tags_p.appendChild(document.createTextNode(metadata_text));

    // Adding potential header.
    if(header !== null) {
      this.header_p = document.createElement('p');
      this.header_p.classList.add('log_event_header');
      this.wrapper_div.appendChild(this.header_p);
      this.header_text = header;
      this.header_p.appendChild(document.createTextNode(header));
    }

    // Adding the actual event (convert to JSON string if not a string).
    if(typeof json === 'string'){
      this.text = json;
    } else {
      this.text = JSON.stringify(json);
    }
    this.data_pre.appendChild(document.createTextNode(this.text));

    // Fold the 'pre' if it is too large and add a button.
    var nb_lines = this.data_pre.innerHTML.split('\n').length;
    if(nb_lines > 4){
      this.large = true;
      this.toggle_folded();
      this.wrapper_div.classList.add('log_event_large');

      var button_p = document.createElement('p');
      button_p.classList.add('p_button_pre');
      var button = document.createElement('button');
      button.appendChild(document.createTextNode('fold / unfold'));
      this.wrapper_div.appendChild(button_p);
      button_p.appendChild(button);
      button.onclick = () => this.toggle_folded();
    }

    this.wrapper_div.appendChild(this.data_pre);
  }

  toggle_folded() {
    this.folded = !this.folded;

    if(this.folded) {
      this.data_pre.classList.add('folded');
    } else {
      this.data_pre.classList.remove('folded');
    }
  }

  set_fold(b) {
    if(b != this.folded) this.toggle_folded();
  }

  matches(regexp) {
    if(this.header_text !== null) {
      var i = this.header_text.search(regexp);
      if(i >= 0) return true;
    }

    var i = this.text.search(regexp);
    return (i >= 0);
  }

  focus() {
    if(this.parent_span !== null) this.parent_span.set_focus(true);
    this.wrapper_div.classList.add('focused');
    this.scroll_into_view();
  }

  unfocus() {
    if(this.parent_span !== null) this.parent_span.set_focus(false);
    this.wrapper_div.classList.remove('focused');
  }
}

/**
 * Class representing a "log span".
 */
class Span extends LogItem {
  /**
   * @param root - the "div" at the root of the log.
   * @param parent_span - the parent of the item in the log (may be null).
   * @param name - the span name (an identifier).
   * @param uid - the span unique identifier.
   * @param json - JSON data array from which the log item is build.
   * @param metadata - metadata for the span (may be null).
   */
  constructor(root, parent_span, name, uid, json, metadata) {
    super(root, parent_span, json);
    this.wrapper_div.classList.add('log_span');

    this.name = name;
    this.uid = uid;
    this.metadata = metadata;
    this.time = null;
    this.full_time = null;
    this.instr = null;
    this.full_instr = null;
    this.children = new Array(); // Other spans or events.
    this.nb_child_span = 0;
    this.name_span = document.createElement('span');
    this.stats_span = document.createElement('span');
    this.header_div = document.createElement('div');
    this.header_p = document.createElement('p');
    this.contents_div = document.createElement('div');
    this.unfold_b = button_with_label('unfold');
    this.unfold_all_b = button_with_label('unfold all');
    this.fold_all_b = button_with_label('fold all');
    this.delete_b = button_with_label('ignore');
    this.event_count = 0;
    this.initial_event_count = 0;
    this.large_event_count = 0;
    this.span_count = 0;
    this.empty_span_count = 0;
    this.is_span = true;
    this.is_event = false;
    this.contents_added = false;
    this.deleted = false;
    this.unfolding_limit = 0; // Limit for unfold_all (0 = no limit).
    this.is_focused = false;
    this.scroll_to = this.header_div;
    this.empty_spans_hidden = false;

    if(this.metadata !== null) {
      // Set up the full time.
      if(this.metadata.hasOwnProperty('t0') &&
         this.metadata.hasOwnProperty('t1')) {
        var t0 = this.metadata['t0'];
        var t1 = this.metadata['t1'];
        this.full_time = t1 - t0;
        this.time = this.full_time;
        delete this.metadata['t0'];
        delete this.metadata['t1'];
      }

      // Set up the full instruction count.
      if(this.metadata.hasOwnProperty('c0') &&
         this.metadata.hasOwnProperty('c1')) {
        var c0 = this.metadata['c0'];
        var c1 = this.metadata['c1'];
        this.full_instr = c1 - c0;
        this.instr = this.full_instr;
        delete this.metadata['c0'];
        delete this.metadata['c1'];
      }
    }

    // Recursively constructing the children.
    for(var i in this.json) {
      var json = this.json[i];

      if(json.hasOwnProperty('data')) {
        var h = null;
        var d = json['data'];
        if(json.hasOwnProperty('header')) {
          h = json['header'];
        } else if (d.hasOwnProperty('header')) {
          h = d['header'];
          d = d['data'];
        }
        var o = new Event(this.root, this, h, d, json['meta']);
        this.event_count++;
        if(o.large) this.large_event_count++;
      } else if(json.hasOwnProperty('name')) {
        var name = json['name'];
        var uid = json['uid'];
        var items = json['items'];
        var metadata = json['meta'];
        var o = new Span(this.root, this, name, uid, items, metadata);
        this.nb_child_span++;
        this.event_count += o.event_count;
        this.large_event_count += o.large_event_count;
        this.span_count += o.span_count + 1;
        this.empty_span_count += o.empty_span_count;
        if(this.time !== null && o.full_time !== null) {
          this.time -= o.full_time;
        }
        if(this.instr !== null && o.full_instr !== null) {
          this.instr -= o.full_instr;
        }
      } else {
        console.log('Not an event nor a span.');
      }
    }

    // Save the real event count to implement hiding of empty spans.
    this.initial_event_count = this.event_count;

    if(this.json.length == 0) this.empty_span_count++;
    this.span_count++;

    // Putting the elements together.
    this.wrapper_div.appendChild(this.header_div);
    this.header_div.appendChild(this.header_p);
    this.header_p.appendChild(this.name_span);

    // Adding CSS classes to the elements.
    this.header_div.classList.add('log_span_header');
    this.header_p.classList.add('log_span_header');
    this.contents_div.classList.add('log_span_contents');

    // Add the prefix and name to the header.
    this.name_span.appendChild(this.prefix());
    this.name_span.appendChild(document.createTextNode(this.name));
    this.name_span.classList.add('span_name');

    // If the span is empty, extend the header and hide the unfolding button.
    if(this.children.length == 0) {
      this.header_p.appendChild(document.createTextNode(" (empty)"));
      this.unfold_b.style.display = 'none';
      this.unfold_all_b.style.display = 'none';
      this.fold_all_b.style.display = 'none';
      this.delete_b.style.display = 'none';
      this.stats_span.style.display = 'none';
    }

    // Install the handlers for the buttons.
    this.unfold_b.onclick = () => this.toggle_contents();
    this.unfold_all_b.onclick = () => this.unfold_all();
    this.fold_all_b.onclick = () => this.fold_all();
    this.delete_b.onclick = () => this.toggle_deleted();

    // If the span has timing data, add it.
    if(this.time !== null && this.full_time !== null) {
      // A span for the whole data, with leading comma.
      var time_info_span = document.createElement('span');
      time_info_span.classList.add('span_time');
      this.header_p.appendChild(time_info_span);

      time_info_span.appendChild(document.createTextNode(", "));

      // Add real time.
      var time = this.time / 1000; // Unit is now ms.
      var real_ts = document.createElement('span');
      real_ts.appendChild(document.createTextNode(`${time.toFixed(3)}ms`));
      if(time >= 50) real_ts.classList.add('large_time');
      time_info_span.appendChild(real_ts);

      if(this.nb_child_span > 0) {
        time_info_span.appendChild(document.createTextNode(" / "));

        // Add full time.
        var full = this.full_time / 1000; // Unit is now ms.
        var full_ts = document.createElement('span');
        full_ts.appendChild(document.createTextNode(`${full.toFixed(3)}ms`));
        if(full >= 50) full_ts.classList.add('large_time');
        time_info_span.appendChild(full_ts);
      }
    }

    // If the span has instruction count data, add it.
    if(this.instr !== null && this.full_instr !== null) {
      // A span for the whole data, with leading comma.
      var instr_info_span = document.createElement('span');
      instr_info_span.classList.add('span_time');
      this.header_p.appendChild(instr_info_span);

      instr_info_span.appendChild(document.createTextNode(", "));

      // Add real instruction count.
      var instr = this.instr / 1000000; // Unit is now Mi.
      var real_ts = document.createElement('span');
      real_ts.appendChild(document.createTextNode(`${instr.toFixed(3)}Mi`));
      if(instr >= 400) real_ts.classList.add('large_time');
      instr_info_span.appendChild(real_ts);

      if(this.nb_child_span > 0) {
        instr_info_span.appendChild(document.createTextNode(" / "));

        // Add full instruction count.
        var full = this.full_instr / 1000000; // Unit is now Mi.
        var full_ts = document.createElement('span');
        full_ts.appendChild(document.createTextNode(`${full.toFixed(3)}Mi`));
        if(full >= 400) full_ts.classList.add('large_time');
        instr_info_span.appendChild(full_ts);
      }
    }

    // Add the stats to the header.
    this.header_p.appendChild(this.stats_span);
    this.stats_span.classList.add('span_stats');
    this.update_stats();

    // Add the remaining metadata to the header.
    if(this.metadata !== null && Object.keys(this.metadata).length > 0) {
      var metadata_info_span = document.createElement('span');
      metadata_info_span.classList.add('span_time');
      this.header_p.appendChild(metadata_info_span);

      var metadata_text = "";
      for(var k in this.metadata) {
        var v = this.metadata[k];
        if(typeof json !== 'string') v = JSON.stringify(v);
        metadata_text += ", " + k + "=" + v;
      }
      metadata_info_span.appendChild(document.createTextNode(metadata_text));
    }

    // Add the buttons to their own span, and the span to the header.
    var buttons_span = document.createElement('span');
    buttons_span.classList.add('span_buttons');
    buttons_span.appendChild(this.unfold_b);
    buttons_span.appendChild(this.unfold_all_b);
    buttons_span.appendChild(this.fold_all_b);
    buttons_span.appendChild(this.delete_b);
    this.header_p.appendChild(buttons_span);
  }

  iter_ancestors(f, current_too=false) {
    if(this.parent_span !== null) this.parent_span.iter_ancestors(f, true);
    if(current_too) f(this);
  }

  iter_spans(f, max_depth=Number.MAX_SAFE_INTEGER) {
    if(max_depth == 0) return;

    if(f(this)) {
      for(var i in this.children) {
        var child = this.children[i];
        if(!child.is_span) continue;
        child.iter_spans(f, max_depth-1);
      }
    }
  }

  iter_events(f, skip_deleted=false, only_added=false,
                              max_depth=Number.MAX_SAFE_INTEGER) {
    if(skip_deleted && this.deleted) return;
    if(only_added && !this.contents_added) return;
    if(max_depth == 0) return;

    for(var i in this.children) {
      var child = this.children[i];
      if(!child.is_span) {
        f(child);
      } else {
        child.iter_events(f, skip_deleted, only_added, max_depth-1);
      }
    }
  }

  events_matching(regexp) {
    var events = new Array();
    var f = function(e) {
      if(e.matches(regexp)) events.push(e);
    };
    this.iter_events(f, true);
    return events;
  }

  set_focus(b) {
    if(this.is_focused == b) return;
    this.is_focused = b;
    if(this.is_focused) {
      this.wrapper_div.classList.add('focused');
    } else {
      this.wrapper_div.classList.remove('focused');
    }
  }

  prefix() {
    var prefix_span = document.createElement('span');
    prefix_span.classList.add('span_prefix');
    var f = function(s) {
      var elem_span = document.createElement('span');
      elem_span.classList.add('span_prefix_part');
      elem_span.appendChild(document.createTextNode(s.name));
      elem_span.onclick = () => s.scroll_into_view();
      prefix_span.appendChild(elem_span);
      prefix_span.appendChild(document.createTextNode(":"));
    }
    this.iter_ancestors(f);
    return prefix_span;
  }

  set_unfolding_limit(limit) {
    var f = function(s) { s.unfolding_limit = limit; return true; };
    this.iter_spans(f);
  }

  update_stats() {
    while(this.stats_span.firstChild) {
      this.stats_span.removeChild(this.stats_span.firstChild);
    }
    this.stats_span.appendChild(document.createTextNode(`, \
      ${this.span_count} spans (${this.empty_span_count} empty) and \
      ${this.event_count} events (${this.large_event_count} large)`));
  }

  offset_parent_counts(ec, lec, sc, esc) {
    if(this.parent_span !== null) {
      this.parent_span.event_count += ec;
      this.parent_span.large_event_count += lec;
      this.parent_span.span_count += sc;
      this.parent_span.empty_span_count += esc;
      this.parent_span.update_stats();
      this.parent_span.offset_parent_counts(ec, lec, sc, esc);
    }
  }

  append_child(o) {
    this.children.push(o);
    this.contents_div.appendChild(o.wrapper_div);
  }

  toggle_contents() {
    this.contents_added = !this.contents_added;

    if(!this.deleted) {
      if(this.contents_added) {
        this.wrapper_div.appendChild(this.contents_div);
        this.unfold_b.innerHTML = 'fold';
      } else {
        this.wrapper_div.removeChild(this.contents_div);
        this.unfold_b.innerHTML = 'unfold';
      }
    }
  }

  set_contents(b) {
    if(b != this.contents_added) this.toggle_contents();
  }

  toggle_deleted() {
    this.deleted = !this.deleted;

    if(this.deleted) {
      if(this.contents_added) this.wrapper_div.removeChild(this.contents_div);
      this.name_span.classList.add('deleted');
      this.delete_b.innerHTML = 'use';
      this.offset_parent_counts(-this.event_count, -this.large_event_count,
        -this.span_count, -this.empty_span_count);
      this.stats_span.style.display = 'none';
    } else {
      if(this.contents_added) this.wrapper_div.appendChild(this.contents_div);
      this.name_span.classList.remove('deleted');
      this.delete_b.innerHTML = 'ignore';
      this.offset_parent_counts(+this.event_count, +this.large_event_count,
        +this.span_count, +this.empty_span_count);
      this.stats_span.style.display = 'inline';
    }
  }

  set_deleted(b) {
    if(b != this.deleted) this.toggle_deleted();
  }

  set_fold_all(b) {
    var f = function(s) { s.set_contents(!b); return true; };
    this.iter_spans(f);
  }

  fold_all() {
    this.set_fold_all(true);
  }

  unfold_all() {
    if(this.unfolding_limit != 0 && this.event_count > this.unfolding_limit) {
      var c = this.event_count;
      var l = this.unfolding_limit;
      alert(`Aborting: there are ${c} events and the limit is ${l}.`);
      return;
    }
    this.set_fold_all(false);
  }

  unfold_to_level(i) {
    var f = function(s) {
      if(s.deleted) return false;
      s.set_contents(true);
      return true;
    };
    this.iter_spans(f, i);
  }

  set_deleted_spans_with_name(name, b) {
    var f = function(s) {
      var name_matches = s.name === name;
      if(s.deleted && !name_matches) return false;
      if(name_matches) s.set_deleted(b);
      return true;
    };
    this.iter_spans(f);
  }

  unfold() {
    this.set_contents(true);
    if(this.parent_span !== null) this.parent_span.unfold();
  }

  hide_empty_spans(b) {
    if(this.empty_spans_hidden == b) return;
    this.empty_spans_hidden = b;

    var f = (s) => {
      if(s.initial_event_count == 0) {
        if(b) {
          s.wrapper_div.classList.add('hidden_empty_span');
        } else {
          s.wrapper_div.classList.remove('hidden_empty_span');
        }
      }

      return true;
    };

    this.iter_spans(f);
  }
}

/**
 * Class implementing a search bar.
 */
class Search {
  constructor(parent_element, root_span) {
    this.parent_element = parent_element;
    this.root_span = root_span;
    this.wrapper_span = document.createElement('span');
    this.input = document.createElement('input');
    this.button = document.createElement('button');
    this.prev_b = document.createElement('button');
    this.next_b = document.createElement('button');
    this.info_span = document.createElement('span');
    this.time_span = document.createElement('span');
    this.warn_span = document.createElement('span');
    this.search_in_progress = false;
    this.events = null;
    this.parents = null;
    this.overall_time = null;
    this.focused = -1;

    // Putting the search bar together.
    this.wrapper_span.appendChild(this.input);
    this.wrapper_span.appendChild(this.button);
    this.wrapper_span.appendChild(this.prev_b);
    this.wrapper_span.appendChild(this.info_span);
    this.wrapper_span.appendChild(this.next_b);
    this.wrapper_span.appendChild(this.time_span);
    this.input.type = 'text';
    this.input.placeholder = 'regexp';
    this.info_span.classList.add('search_info');
    this.time_span.classList.add('search_time');
    this.warn_span.classList.add('search_warn');
    this.prev_b.innerHTML = '&lt;';
    this.next_b.innerHTML = '&gt;';

    // Setting the initial state for the elements.
    this.button.innerHTML = 'search';
    this.prev_b.style.display = 'none';
    this.next_b.style.display = 'none';
    this.info_span.style.display = 'none';
    this.time_span.style.display = 'none';
    this.warn_span.style.display = 'none';

    // Pressing enter in the search field triggers the search.
    this.input.onkeypress = (e) => {
      if(e.key === "Enter") {
        e.preventDefault();
        this.run_search();
      }
    };

    // Adding the other handlers.
    this.button.onclick = () => this.run_search();
    this.prev_b.onclick = () => this.focus_prev();
    this.next_b.onclick = () => this.focus_next();

    // Add the search bar to the parent element.
    this.parent_element.appendChild(this.wrapper_span);
  }

  focus_event(i) {
    if(i == this.focused) return;
    if(this.focused >= 0) {
      this.events[this.focused].unfocus();
    }

    if(i >= this.events.length) return;

    this.focused = i;
    this.events[this.focused].focus();
    this.info_span.innerHTML = `${i+1} / ${this.events.length}`
  }

  focus_prev() {
    if(this.focused < 0) return;
    let prev = (this.focused - 1 + this.events.length) % this.events.length;
    this.focus_event(prev);
  }

  focus_next() {
    if(this.focused < 0) return;
    let next = (this.focused + 1) % this.events.length;
    this.focus_event(next);
  }

  run_search() {
    this.input.disabled = true;
    this.button.disabled = true;

    if(this.search_in_progress) {
      for(var i in this.events) {
        this.events[i].set_highlighted(false);
      }

      for(var i in this.parents) {
        this.parents[i].set_highlighted(false);
      }

      this.events = null;
      this.parents = null;
      this.overall_time = null;
      this.focused = -1;
      this.prev_b.style.display = 'none';
      this.next_b.style.display = 'none';
      this.info_span.style.display = 'none';
      this.time_span.style.display = 'none';

      this.root_span.fold_all();

      this.button.innerHTML = 'search';
      this.search_in_progress = false;
      this.input.disabled = false;
      this.button.disabled = false;
      this.input.focus();
    } else {
      var regexp = this.input.value;
      if(regexp.length == 0) {
        alert('Aborting: no regexp given.');
        this.input.disabled = false;
        this.button.disabled = false;
        return;
      }

      this.events = this.root_span.events_matching(new RegExp(regexp));
      this.parents = new Array();
      this.overall_time = 0;

      if(this.events.length == 0) {
        alert('No match found.');
        this.input.disabled = false;
        this.button.disabled = false;
        return;
      }

      this.button.innerHTML = 'clear';
      this.search_in_progress = true;

      var add_parent = (e) => {
        var p = e.parent_span;

        for(var i in this.parents) {
          var pi = this.parents[i];
          if(p === pi) return;
        }

        this.overall_time += p.time;
        p.set_highlighted(true);
        this.parents.push(p);
      };

      // Set match on found events, and collect parent spans for timing.
      for(var i in this.events) {
        this.events[i].set_highlighted(true);
        add_parent(this.events[i]);
      }

      var time = this.overall_time * 1000;
      this.time_span.innerHTML =
        `${time.toFixed(3)}ms (sum of ${this.parents.length} spans)`;

      if(this.events.length > 1) {
        this.next_b.style.display = 'inline';
        this.prev_b.style.display = 'inline';
        this.next_b.focus();
      }

      this.info_span.style.display = 'inline-block';
      this.time_span.style.display = 'inline-block';

      this.focus_event(0);
      this.button.disabled = false;
    }
  }
}

/**
 * Class implementing an add/delete bar.
 */
class AddDelete {
  constructor(parent_element, root_span, value) {
    this.parent_element = parent_element;
    this.root_span = root_span;
    this.initial_input_value = value;
    this.wrapper_span = document.createElement('span');
    this.input = document.createElement('input');
    this.add_b = document.createElement('button');
    this.del_b = document.createElement('button');

    // Putting the delete/add bar together.
    this.wrapper_span.appendChild(this.input);
    this.wrapper_span.appendChild(this.add_b);
    this.wrapper_span.appendChild(this.del_b);
    this.input.type = 'text';
    this.input.placeholder = 'span name';
    this.input.value = this.initial_input_value;
    this.add_b.innerHTML = 'use all';
    this.del_b.innerHTML = 'ignore all';

    // Adding the handlers.
    this.add_b.onclick = () => this.run(false);
    this.del_b.onclick = () => this.run(true);

    // Add the delete/add bar to the parent element.
    this.parent_element.appendChild(this.wrapper_span);
  }

  run(b) {
    this.add_b.disabled = true;
    this.add_b.disabled = true;

    var name = this.input.value;

    if(name.length == 0) {
      alert('Aborting: no span name given.');
      this.add_b.disabled = false;
      this.del_b.disabled = false;
      return;
    }

    this.root_span.set_deleted_spans_with_name(name, b);
    this.add_b.disabled = false;
    this.del_b.disabled = false;
  }
}

function generate_page(target, json) {
  // Adding the contents into a wrapper 'div'.
  var wrapper = document.createElement('div');
  wrapper.classList.add('log_wrapper');
  var log_span = new Span(wrapper, null, 'log', -1, json, null);
  log_span.set_deleted_spans_with_name('ocaml_dnet', true);
  log_span.unfold_to_level(2);
  log_span.hide_empty_spans(true);

  // Control bar.
  var control = document.createElement('p');
  control.classList.add('control_bar');

  // Add a checkbox for limiting span unfolding.
  var limit_span = document.createElement('span');
  limit_span.classList.add('sub_control_bar');
  add_checkbox(limit_span, `limit unfolding to 20000 events`, true,
    b => log_span.set_unfolding_limit(b ? 20000 : 0));
  control.appendChild(limit_span);

  // Add a checkbox for including empty spans.
  var hide_empty_span = document.createElement('span');
  hide_empty_span.classList.add('sub_control_bar');
  add_checkbox(hide_empty_span, `hide empty spans`, false,
    b => log_span.hide_empty_spans(b));
  control.appendChild(hide_empty_span);

  // Adding an add/delete span field.
  var add_del_span = document.createElement('span');
  add_del_span.classList.add('sub_control_bar');
  var add_delete = new AddDelete(add_del_span, log_span, 'ocaml_dnet');
  control.appendChild(add_del_span);

  // Adding a search field.
  var search_span = document.createElement('span');
  search_span.classList.add('sub_control_bar');
  var search = new Search(search_span, log_span);
  control.appendChild(search_span);

  // Adding the generated elements to the target.
  target.appendChild(control);
  target.appendChild(wrapper);
}
