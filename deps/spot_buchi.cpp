#include <sstream>
#include <iostream>
#include <fstream>

#include <jlcxx/jlcxx.hpp>
#include <jlcxx/stl.hpp>
#include <jlcxx/tuple.hpp>
#include <jlcxx/array.hpp>

// these are defined both by jlcxx and buddy
#undef __likely
#undef __unlikely

#include <spot/tl/formula.hh>
#include <spot/tl/parse.hh>
#include <spot/tl/print.hh>
#include <spot/tl/apcollect.hh>
#include <spot/tl/environment.hh>

#include <spot/twa/acc.hh>
#include <spot/twa/twagraph.hh>
#include <spot/twa/formula2bdd.hh>

#include <spot/twaalgos/word.hh>
#include <spot/twaalgos/dot.hh>
#include <spot/twaalgos/isdet.hh>
#include <spot/twaalgos/split.hh>
#include <spot/twaalgos/totgba.hh>
#include <spot/twaalgos/hoa.hh>
#include <spot/twaalgos/sbacc.hh>
#include <spot/twaalgos/postproc.hh>
#include <spot/twaalgos/canonicalize.hh>
#include <spot/twaalgos/product.hh>
#include <spot/twaalgos/complement.hh>
#include <spot/twaalgos/contains.hh>

#include <spot/parseaut/public.hh>

static const char* const DIGIT[] = {
  "⓪","①","②","③","④","⑤","⑥","⑦","⑧","⑨",
  "⑩","⑪","⑫","⑬","⑭","⑮","⑯","⑰","⑱","⑲",
  "⑳","㉑","㉒","㉓","㉔","㉕","㉖","㉗","㉘","㉙",
  "㉚","㉛","㉜","㉝","㉞","㉟","㊱","㊲","㊳","㊴",
  "㊵","㊶","㊷","㊸","㊹","㊺","㊻","㊼","㊽","㊾","㊿"};
			     namespace jlcxx
{
  // this doesn't work because bddxtrue is not polymorphic (has no virtual destructor)
  //  template<> struct SuperType<bddxtrue> { typedef bdd type; };
  //  template<> struct SuperType<bddxfalse> { typedef bdd type; };
  template<> struct SuperType<spot::twa_graph> { typedef spot::twa type; };
  template<> struct IsMirroredType<spot::acc_cond::mark_t> : std::false_type { };
}

JLCXX_MODULE define_julia_module(jlcxx::Module& mod)
{
  // boolean decision formulas.
  mod.add_type<bdd>("BDD")
    .method("id", &bdd::id);
  mod.method("bdd_from_int", [](int i) { return bdd_from_int(i); });
  // mod.add_type<bddxtrue>("BDDTrue",jlcxx::julia_base_type<bdd>());
  // mod.add_type<bddxfalse>("BDDFalse",jlcxx::julia_base_type<bdd>());
  mod.method("bdd_init", [](unsigned nodesize, unsigned cachesize) { return bdd_init(nodesize, cachesize); });
  mod.method("bdd_extvarnum", [](unsigned n) { return bdd_extvarnum(n); });
  mod.method("bdd_ithvar", [](unsigned n) { return bdd_ithvar(n); });
  mod.method("bdd_var", [](bdd b) { return bdd_var(b); });
  mod.method("bdd_var", [](unsigned b) { return bdd_var((BDD)b); });
  mod.method("bdd_true", []() { return bdd(bdd_true()); }); // cannot use bbbxtrue type
  mod.method("bdd_false", []() { return bdd(bdd_false()); });
  mod.method("bdd_not", [](bdd b) { return bdd_not(b); });
  mod.method("bdd_apply", [](bdd b, bdd c, int n) { return bdd_apply(b,c,n); });
  mod.method("bdd_and", [](bdd b, bdd c) { return bdd_and(b,c); });
  mod.method("bdd_or", [](bdd b, bdd c) { return bdd_or(b,c); });
  mod.method("bdd_xor", [](bdd b, bdd c) { return bdd_xor(b,c); });
  mod.method("bdd_imp", [](bdd b, bdd c) { return bdd_imp(b,c); });
  mod.method("bdd_biimp", [](bdd b, bdd c) { return bdd_biimp(b,c); });
  // setxor, implies, etc.

  // formula
  mod.add_type<spot::formula>("Formula");
  
  // trival
  mod.add_bits<spot::trival::value_t>("TriValue", jlcxx::julia_type("CppEnum"));
  mod.set_const("no", spot::trival::no_value);
  mod.set_const("yes", spot::trival::yes_value);
  mod.set_const("maybe", spot::trival::maybe_value);
  mod.add_type<spot::trival>("Trival")
    .constructor<bool>()
    .constructor<spot::trival::value_t>()
    .method("is_known", &spot::trival::is_known)
    .method("is_maybe", &spot::trival::is_maybe)
    .method("is_true", &spot::trival::is_true)
    .method("is_false", &spot::trival::is_false)
    .method("TriValue", &spot::trival::val)
    .method("Bool", &spot::trival::operator bool);
  mod.set_override_module(jl_base_module);
  mod.method("!", [](spot::trival x) { return !x; }); // cannot directly add method to Base :(
  mod.unset_override_module();
 
  // dictionary of BDDs.
  mod.add_type<spot::bdd_dict>("BDDDict")
    .method("register_anonymous_variables", [](spot::bdd_dict_ptr d, unsigned n) { return d->register_anonymous_variables(n, NULL); })
    .method("dump", [](spot::bdd_dict_ptr d) { d->dump(std::cerr); });
  mod.method("make_bdd_dict", spot::make_bdd_dict);

  mod.method("string_psl", [](bdd b, spot::bdd_dict_ptr d) { std::stringstream s; spot::print_psl(s, spot::bdd_to_formula(b,d)); return s.str(); });
  
  // acceptance condition
  mod.add_type<spot::acc_cond>("AccCond")
    .method("name", &spot::acc_cond::name);

  // acceptance mark_t
  mod.add_type<spot::acc_cond::mark_t>("MarkT")
    .method("new_mark_t", [](std::vector<unsigned> &v) { return spot::acc_cond::mark_t(v.begin(), v.end()); })
    .method("count", &spot::acc_cond::mark_t::count)
    .method("fill", [](spot::acc_cond::mark_t &m) { std::vector<unsigned> v; m.fill(std::back_inserter(v)); return v; });

  // acceptance code
  mod.add_type<spot::acc_cond::acc_code>("AccCode")
    .method("is_dnf", &spot::acc_cond::acc_code::is_dnf)
    .method("to_text", [](spot::acc_cond::acc_code &ac) {
      std::stringstream s;
      ac.to_text(s, [](std::ostream& os, int v) { os << "<FONT COLOR=\"Green\">" << DIGIT[v] << "</FONT>"; });
      return s.str();
    })
    .method("complement", &spot::acc_cond::acc_code::complement);
  mod.method("buchi", &spot::acc_cond::acc_code::buchi);
  mod.method("cobuchi", &spot::acc_cond::acc_code::cobuchi);
  // complement
  mod.method("f", &spot::acc_cond::acc_code::f);
  // mod.method("fin", &spot::acc_cond::acc_code::fin);
  // mod.method("fin_neg", &spot::acc_cond::acc_code::fin_neg);
  // fin_one
  // fin_one_extract
  // fin_unit
  // fin_unit_one_split
  // fin_unit_one_split_improved
  // force_inf
  mod.method("generalized_buchi", &spot::acc_cond::acc_code::generalized_buchi);
  mod.method("generalized_co_buchi", &spot::acc_cond::acc_code::generalized_co_buchi);
  // generalized_rabin
  // inf, inf_neg, inf_satisfiable, inf_unit, is_cnf
  // is_f, is_t, mafins, maybe_accepting, missing
  // operators &, &=, <<, <<=, |, |=
  mod.method("parity", &spot::acc_cond::acc_code::parity);
  mod.method("parity_max", &spot::acc_cond::acc_code::parity_max);
  mod.method("parity_max_even", &spot::acc_cond::acc_code::parity_max_even);
  mod.method("parity_max_odd", &spot::acc_cond::acc_code::parity_max_odd);
  mod.method("parity_min", &spot::acc_cond::acc_code::parity_min);
  mod.method("parity_min_even", &spot::acc_cond::acc_code::parity_min_even);
  mod.method("parity_min_odd", &spot::acc_cond::acc_code::parity_min_odd);
  mod.method("rabin", &spot::acc_cond::acc_code::rabin);
  // random, remove
  mod.method("streett", &spot::acc_cond::acc_code::streett);
  // strip, symmetries
  mod.method("t", &spot::acc_cond::acc_code::t);
  // to_bdd, to_cnf, to_dnf, to_html, to_latex
  // top_conjuncts, top_disjuncts, used_inf_fin_sets
  // used_once_sets, used_sets, useless_color_patterns
  
  // twa
  mod.add_type<spot::twa>("TWA")
    .method("acc", [](spot::twa_ptr aut) { return aut->acc(); })
    .method("register_ap", [](spot::twa_ptr aut, std::string ap) { return aut->register_ap(ap); })
    // register_ap(formula)
    .method("register_aps_from_dict", [](spot::twa_ptr aut) { return aut->register_aps_from_dict(); })
    .method("get_dict", [](spot::twa_ptr aut) { return aut->get_dict(); })
    .method("get_acceptance", [](spot::twa_ptr aut) { return aut->get_acceptance(); })
    .method("set_acceptance!", [](spot::twa_ptr aut, unsigned num, const spot::acc_cond::acc_code &c) { return aut->set_acceptance(num, c); })
    .method("set_acceptance!", [](spot::twa_ptr aut, const spot::acc_cond::acc_code &c) { return aut->set_acceptance(c); })
    .method("set_generalized_buchi!", [](spot::twa_ptr aut, unsigned n) { return aut->set_generalized_buchi(n); })
    .method("set_generalized_co_buchi!", [](spot::twa_ptr aut, unsigned n) { return aut->set_generalized_co_buchi(n); })
    .method("set_buchi!", [](spot::twa_ptr aut) { return aut->set_buchi(); })
    .method("set_co_buchi!", [](spot::twa_ptr aut) { return aut->set_co_buchi(); })
    ;
  
  // twa_word
  mod.add_type<spot::twa_word>("TWAWord")
    .constructor<spot::bdd_dict_ptr>()
    .method("make_twa_word", [](spot::bdd_dict_ptr dict) { return spot::make_twa_word(dict); })
    .method("push_prefix!", [](spot::twa_word_ptr w, bdd v) { w->prefix.push_back(v); })
    .method("push_cycle!", [](spot::twa_word_ptr w, bdd v) { w->cycle.push_back(v); })
    .method("append_prefix!", [](spot::twa_word_ptr w, jlcxx::ArrayRef<unsigned> v) { for (auto x: v) w->prefix.push_back(bdd_from_int(x)); })
    .method("append_cycle!", [](spot::twa_word_ptr w, jlcxx::ArrayRef<unsigned> v) { for (auto x: v) w->cycle.push_back(bdd_from_int(x)); })
    .method("get_prefix_cycle", [](spot::twa_word_ptr w, jlcxx::ArrayRef<unsigned> _prefix, jlcxx::ArrayRef<unsigned> _cycle) { // we return vectors of unsigned, CxxWrap is not capable of handling vectors of weirder stuff
      // (we'll convert them back to BDDs using bdd_from_int)
      for (auto &t : w->prefix)
	_prefix.push_back(t.id());
      for (auto &t : w->cycle)
	_cycle.push_back(t.id());	  
    });

  // twa_run
  mod.add_type<spot::twa_run>("TWARun")
    .method("get_prefix_cycle", [](spot::twa_run_ptr w, jlcxx::ArrayRef<size_t> _prefix, jlcxx::ArrayRef<size_t> _cycle) {
      for (auto &t : w->prefix)
	_prefix.push_back(t.s->hash());
      for (auto &t : w->cycle)
	_cycle.push_back(t.s->hash()); // and t.label and t.acc !
    });

  typedef spot::twa_graph::graph_t graph_t;
  
  // edge iterator
  mod.add_type<spot::internal::edge_iterator<graph_t>>("TWAEdgeIterator")
    .method("incr", [](spot::internal::edge_iterator<graph_t> iter) { return ++iter; })
    .method("get", [](spot::internal::edge_iterator<graph_t> iter) { return std::make_tuple(iter->src,iter->cond,iter->dst,iter->acc); });

  // out-edges from a vertex
  mod.add_type<spot::internal::state_out<graph_t>>("TWAStateOut")
    .method("begin", &spot::internal::state_out<graph_t>::begin)
    .method("end", &spot::internal::state_out<graph_t>::end)
    .method("isdone", [](spot::internal::state_out<graph_t> &so, spot::internal::edge_iterator<graph_t> &iter) { return iter == so.end(); });

  // all-edge iterator
  mod.add_type<spot::internal::all_edge_iterator<graph_t>>("TWAAllEdgeIterator")
    .method("incr", [](spot::internal::all_edge_iterator<graph_t> iter) { return ++iter; })
    .method("get", [](spot::internal::all_edge_iterator<graph_t> iter) { return std::make_tuple(iter->src,iter->cond,iter->dst,iter->acc); });

  // all transitions
  mod.add_type<spot::internal::all_trans<graph_t>>("TWAAllTrans")
    .method("begin", &spot::internal::all_trans<graph_t>::begin)
    .method("end", &spot::internal::all_trans<graph_t>::end)
    .method("isdone", [](spot::internal::all_trans<spot::twa_graph::graph_t> &so, spot::internal::all_edge_iterator<graph_t> &iter) { return iter == so.end(); });
  
  // twa_graph
  mod.add_type<spot::twa_graph>("TWAGraph",jlcxx::julia_base_type<spot::twa>());
    // get_graph
  mod.method("acc", [](spot::twa_graph_ptr aut) { return aut->acc(); }); // added from twa, we don't have covariance on SharedPtrAllocated
  mod.method("num_states", [](spot::twa_graph_ptr aut) { return aut->num_states(); });
  mod.method("num_edges", [](spot::twa_graph_ptr aut) { return aut->num_edges(); }); // &spot::twa_graph::num_edges)
  mod.method("set_init_state!", [](spot::twa_graph_ptr aut, unsigned n) { return aut->set_init_state(n); });
    // set_univ_init_state
  mod.method("get_init_state_number", [](spot::twa_graph_ptr aut) { return aut->get_init_state_number(); });
    // get_init_state
    // succ_iter
    // state_number
    // state_from_number
    // format_state
    // edge_number
    // edge_data
    // edge_storage
  mod.method("new_state!", [](spot::twa_graph_ptr aut) { return aut->new_state(); });
  mod.method("new_states!", [](spot::twa_graph_ptr aut, unsigned n) { return aut->new_states(n); });
  mod.method("new_edge!", [](spot::twa_graph_ptr aut, unsigned src, unsigned dst, bdd cond) { return aut->new_edge(src, dst, cond); });
  mod.method("new_edge!", [](spot::twa_graph_ptr aut, unsigned src, unsigned dst, bdd cond, spot::acc_cond::mark_t acc = {}) { return aut->new_edge(src, dst, cond, acc); });    
  mod.method("new_edge!", [](spot::twa_graph_ptr aut, unsigned src, unsigned dst, bdd cond, unsigned accept) {
      return aut->new_edge(src, dst, cond, {accept});
    });
  mod.method("new_edge!", [](spot::twa_graph_ptr aut, unsigned src, unsigned dst, bdd cond, jlcxx::ArrayRef<unsigned> _accept) {
      spot::acc_cond::mark_t accept(_accept.begin(), _accept.end());
      return aut->new_edge(src, dst, cond, accept);
    });
  mod.method("new_acc_edge!", [](spot::twa_graph_ptr aut, unsigned src, unsigned dst, bdd cond, bool acc = true) { return aut->new_acc_edge(src, dst, cond, acc); });
    // new_univ_edge
  mod.method("out", [](spot::twa_graph_ptr aut, unsigned s) { return aut->out(s); });
  mod.method("edges", [](spot::twa_graph_ptr aut) { return aut->edges(); });
    // out_iteraser
    // univ_dests
  mod.method("is_existential", [](spot::twa_graph_ptr aut) { return aut->is_existential(); });
    // states
    // edge_vector
    // is_dead_edge
  mod.method("merge_edges!", [](spot::twa_graph_ptr aut) { return aut->merge_edges(); });
  mod.method("merge_univ_dests!", [](spot::twa_graph_ptr aut) { return aut->merge_univ_dests(); });
    // merge_states
    // merge_states_of
  mod.method("purge_dead_states!", [](spot::twa_graph_ptr aut, unsigned n) { return aut->purge_dead_states(); });
    // purge_unreachable_states
    // remove_unused_ap
    // copy_state_names_from
    // state_acc_sets
  mod.method("===", [](spot::twa_graph_ptr me, spot::twa_graph_ptr you) { return *me == *you; });
  mod.method("kill_state!", [](spot::twa_graph_ptr aut, unsigned state) { return aut->kill_state(state); });
    // dump_storage_as_dot
    // succ
    // release_iter
  mod.method("get_dict", [](spot::twa_graph_ptr aut) { return aut->get_dict(); });
    // unregister_ap
    // register_aps_from_dict
  mod.method("ap", [](spot::twa_graph_ptr aut) { jl_error("bug: StdFill missing"); /*return aut->ap();*/ });
  mod.method("ap_vars", [](spot::twa_graph_ptr aut) { return aut->ap_vars(); });
    // project_state
  mod.method("is_empty", [](spot::twa_graph_ptr aut) { return aut->is_empty(); });
  mod.method("accepting_run", [](spot::twa_graph_ptr aut) { return aut->accepting_run(); });
  mod.method("accepting_word", [](spot::twa_graph_ptr aut) { return aut->accepting_word(); });
  mod.method("intersects", [](spot::twa_graph_ptr aut, spot::twa_ptr other) { return aut->intersects(other); }); // !!! or twa_graph_ptr other?
  mod.method("intersects", [](spot::twa_graph_ptr aut, spot::twa_word_ptr other) { return aut->intersects(other); });
  mod.method("intersecting_run", [](spot::twa_graph_ptr aut, spot::twa_graph_ptr other) { return aut->intersecting_run(other); });
  mod.method("intersecting_word", [](spot::twa_graph_ptr aut, spot::twa_graph_ptr other) { return aut->intersecting_word(other); });
  mod.method("exclusive_run", [](spot::twa_graph_ptr aut, spot::twa_graph_ptr other) { return aut->exclusive_run(other); });
  mod.method("exclusive_word", [](spot::twa_graph_ptr aut, spot::twa_graph_ptr other) { return aut->exclusive_word(other); });
  mod.method("num_sets", [](spot::twa_graph_ptr aut) { return aut->num_sets(); });
  mod.method("get_acceptance", [](spot::twa_graph_ptr aut) { return aut->get_acceptance(); });
  mod.method("set_acceptance!", [](spot::twa_graph_ptr aut, unsigned num, const spot::acc_cond::acc_code &c) { return aut->set_acceptance(num, c); });
  mod.method("set_acceptance!", [](spot::twa_graph_ptr aut, const spot::acc_cond::acc_code &c) { return aut->set_acceptance(c); });
  mod.method("copy_acceptance_of", [](spot::twa_graph_ptr me, spot::twa_graph_ptr you) { return me->copy_acceptance_of(you); });
  mod.method("copy_ap_of", [](spot::twa_graph_ptr me, spot::twa_graph_ptr you) { return me->copy_ap_of(you); });
    // copy_named_properties_of
  mod.method("set_generalized_buchi!", [](spot::twa_graph_ptr aut, unsigned n) { return aut->set_generalized_buchi(n); });
  mod.method("set_generalized_co_buchi!", [](spot::twa_graph_ptr aut, unsigned n) { return aut->set_generalized_co_buchi(n); });
  mod.method("set_buchi!", [](spot::twa_graph_ptr aut) { return aut->set_buchi(); });
  mod.method("set_co_buchi!", [](spot::twa_graph_ptr aut) { return aut->set_co_buchi(); });
    // set_named_prop
    // get_named_prop
    // get_or_set_named_prop
    // release_named_properties
  mod.method("prop_state_acc", [](spot::twa_graph_ptr aut) { return aut->prop_state_acc(); });
  mod.method("prop_state_acc!", [](spot::twa_graph_ptr aut, spot::trival val) { return aut->prop_state_acc(val); });
  mod.method("is_sba", [](spot::twa_graph_ptr aut) { return aut->is_sba(); });
  mod.method("prop_inherently_weak", [](spot::twa_graph_ptr aut) { return aut->prop_inherently_weak(); });
  mod.method("prop_terminal", [](spot::twa_graph_ptr aut) { return aut->prop_terminal(); });
  mod.method("prop_weak", [](spot::twa_graph_ptr aut) { return aut->prop_weak(); });
  mod.method("prop_very_weak", [](spot::twa_graph_ptr aut) { return aut->prop_very_weak(); });
  mod.method("prop_complete", [](spot::twa_graph_ptr aut) { return aut->prop_complete(); });
  mod.method("prop_universal", [](spot::twa_graph_ptr aut) { return aut->prop_universal(); });
  mod.method("prop_unambiguous", [](spot::twa_graph_ptr aut) { return aut->prop_unambiguous(); });
  mod.method("prop_semi_deterministic", [](spot::twa_graph_ptr aut) { return aut->prop_semi_deterministic(); });
  mod.method("prop_stutter_invariant", [](spot::twa_graph_ptr aut) { return aut->prop_stutter_invariant(); });
  mod.method("state_is_accepting", [](spot::twa_graph_ptr aut, unsigned s) { return aut->state_is_accepting(s); }); // state*
    // defrag_states
  mod.method("register_ap", [](spot::twa_graph_ptr aut, std::string ap) { return aut->register_ap(ap); });
    // acc
  mod.method("product", [](spot::twa_graph_ptr left, spot::twa_graph_ptr right) { return spot::product(left,right); });
  mod.method("product_or", [](spot::twa_graph_ptr left, spot::twa_graph_ptr right) { return spot::product_or(left,right); });
  mod.method("product_xor", [](spot::twa_graph_ptr left, spot::twa_graph_ptr right) { return spot::product_xor(left,right); });
  mod.method("product_xnor", [](spot::twa_graph_ptr left, spot::twa_graph_ptr right) { return spot::product_xnor(left,right); });
  mod.method("complement", [](spot::twa_graph_ptr aut) { return spot::complement(aut); });

  mod.method("contains", [](spot::twa_graph_ptr left, spot::twa_graph_ptr right) { return spot::contains(left,right); });
  mod.method("are_equivalent", [](spot::twa_graph_ptr left, spot::twa_graph_ptr right) { return spot::are_equivalent(left,right); });
  
  mod.method("as_twa", [](spot::twa_run_ptr run) { return run->as_twa(); });
  
  mod.method("canonicalize", spot::canonicalize);
  mod.method("split_edges", spot::split_edges);

  mod.method("string_dot", [](spot::twa_graph_ptr aut, std::string options) {
    std::ostringstream buffer;
    spot::print_dot(buffer, aut, options.c_str());
    return buffer.str();
  });

  mod.method("string_hoa", [](spot::twa_graph_ptr aut) {
    std::ostringstream buffer;
    spot::print_hoa(buffer, aut);
    return buffer.str();
  });

  mod.method("save_hoa", [](std::string filename, spot::twa_graph_ptr aut) {
    std::ofstream stream(filename);
    spot::print_hoa(stream, aut);
    stream << std::endl;
  });
  
  mod.method("parse_hoa_string", [](std::string str, spot::bdd_dict_ptr dict) {
    auto p = spot::automaton_stream_parser(str.c_str(), "<julia>");
    auto aut = p.parse(dict);
    return aut->aut;
  });

  mod.method("parse_hoa", [](std::string filename, spot::bdd_dict_ptr dict) {
    auto p = spot::automaton_stream_parser(filename);
    auto aut = p.parse(dict);
    return aut->aut;
  });
  
  mod.method("as_automaton", [](spot::twa_word_ptr w) { return w->as_automaton(); });
  mod.method("intersects", [](spot::twa_word_ptr w, spot::const_twa_ptr aut) { return w->intersects(aut); });
  mod.method("intersects", [](spot::twa_word_ptr w, spot::const_twa_graph_ptr aut) { return w->intersects(aut); });
  mod.method("make_twa_graph", [](const spot::bdd_dict_ptr dict) { return spot::make_twa_graph(dict); });

  mod.add_bits<spot::postprocessor::output_type>("OutputType");
  mod.set_const("OT_TGBA", spot::postprocessor::output_type::TGBA);
  mod.set_const("OT_GeneralizedBuchi", spot::postprocessor::output_type::GeneralizedBuchi);
  mod.set_const("OT_BA", spot::postprocessor::output_type::BA);
  mod.set_const("OT_Monitor", spot::postprocessor::output_type::Monitor);
  mod.set_const("OT_Generic", spot::postprocessor::output_type::Generic);
  mod.set_const("OT_Parity", spot::postprocessor::output_type::Parity);
  mod.set_const("OT_ParityMin", spot::postprocessor::output_type::ParityMin);
  mod.set_const("OT_ParityMax", spot::postprocessor::output_type::ParityMax);
  mod.set_const("OT_ParityOdd", spot::postprocessor::output_type::ParityOdd);
  mod.set_const("OT_ParityEven", spot::postprocessor::output_type::ParityEven);
  mod.set_const("OT_ParityMinOdd", spot::postprocessor::output_type::ParityMinOdd);
  mod.set_const("OT_ParityMaxOdd", spot::postprocessor::output_type::ParityMaxOdd);
  mod.set_const("OT_ParityMinEven", spot::postprocessor::output_type::ParityMinEven);
  mod.set_const("OT_ParityMaxEven", spot::postprocessor::output_type::ParityMaxEven);
  mod.set_const("OT_CoBuchi", spot::postprocessor::output_type::CoBuchi);
  mod.set_const("OT_Buchi", spot::postprocessor::output_type::Buchi);

  mod.set_const("OP_Any", 0 /*spot::postprocessor::Any*/);
  mod.set_const("OP_Small", 1 /*spot::postprocessor::Small*/);
  mod.set_const("OP_Deterministic", 2 /*spot::postprocessor::Deterministic*/);
  mod.set_const("OP_Complete", 4 /*spot::postprocessor::Complete*/);
  mod.set_const("OP_SBAcc", 8 /*spot::postprocessor::SBAcc*/);
  mod.set_const("OP_Unambiguous", 16 /*spot::postprocessor::Unambiguous*/);
  mod.set_const("OP_Colored", 32 /*spot::postprocessor::Colored*/);
  
  mod.add_bits<spot::postprocessor::optimization_level>("OptimizationLevel");
  mod.set_const("OL_Low", spot::postprocessor::optimization_level::Low);
  mod.set_const("OL_Medium", spot::postprocessor::optimization_level::Medium);
  mod.set_const("OL_High", spot::postprocessor::optimization_level::High);

  // post-processor
  mod.add_type<spot::postprocessor>("PostProcessor")
    .constructor<>()
    .method("set_type", &spot::postprocessor::set_type)
    .method("set_pref", &spot::postprocessor::set_pref)
    .method("set_level", &spot::postprocessor::set_level);
  mod.method("run", [](spot::postprocessor post, spot::twa_graph_ptr aut) { return post.run(aut); });

  // apply a letter-to-letter map to the conditions
  mod.method("recode_word", [](spot::twa_word_ptr w, jlcxx::ArrayRef<unsigned> xlator) {
    auto res = make_twa_word(w->get_dict());

    for (auto& t: w->prefix) {
      unsigned id = t.id();
      if (id >= xlator.size())
	jl_error("xlator is too short");
      unsigned newid = xlator[id];
      if (newid == unsigned(-1))
	jl_error("missing value in xlator");
      res->prefix.push_back(bdd_from_int(newid));
    }

    for (auto& t: w->cycle) {
      unsigned id = t.id();
      if (id >= xlator.size())
	jl_error("xlator is too short. Did you remember to split_edges()?");
      unsigned newid = xlator[id];
      if (newid == unsigned(-1))
	jl_error("missing value in xlator. Did you remember to split_edges()?");
      res->cycle.push_back(bdd_from_int(newid));
    }

    return res;
  });
  mod.method("recode_aut", [](spot::twa_graph_ptr aut, spot::twa_graph_ptr model, jlcxx::ArrayRef<unsigned> xlator) {
    auto res = make_twa_graph(aut->get_dict());
    res->copy_ap_of(model);
    res->copy_acceptance_of(aut);
    res->prop_copy(aut, spot::twa::prop_set::all());
    res->new_states(aut->num_states());
    res->set_init_state(aut->get_init_state_number());

    for (auto& t: aut->edges()) {
      unsigned id = t.cond.id();
      if (id >= xlator.size())
	jl_error("xlator is too short. Did you remember to split_edges()?");
      unsigned newid = xlator[id];
      if (newid == unsigned(-1))
	jl_error("missing value in xlator. Did you remember to split_edges()?");
      res->new_edge(t.src, t.dst, bdd_from_int(newid), t.acc);
    }

    return res;
  });
}

#if 0
std::vector<fin_inf_tuple> get_rabin_acceptance(spot::twa_graph &aut)
{
        spot::acc_cond acc = aut.acc();
        std::vector<fin_inf_tuple> fin_inf_vec;
        std::vector<spot::acc_cond::rs_pair> pairs;
        bool israbin = acc.is_rabin_like(pairs);
        // for (auto p: pairs){
        //         std::cout << "hello pair" << std::endl;
        //         std::cout << p.fin << std::endl;
        //         std::cout << p.inf << std::endl;
        // }
        for (auto p: pairs)
        {
                std::vector<unsigned> statefinset;
                std::vector<unsigned> stateinfset;
        
                auto finset = container_to_set(p.fin.sets());
                auto infset = container_to_set(p.inf.sets());

                // std::cout << "print finset" << std::endl;
                // for (auto i : p.fin.sets())
                // {
                //         std::cout << i << std::endl;
                // }
                // std::cout << "print infset" << std::endl;
                // for (auto i : infset)
                // {
                //         std::cout << i << std::endl;
                // }
                // std::cout << "num states" << ns << std::endl;
                for (int s=0; s < aut.num_states(); s++)
                {       
                        // std::cout << "hello state " << s << std::endl;
                        auto stateset = container_to_set(aut.state_acc_sets(s).sets());
                        std::vector<unsigned int> it1;
                        std::vector<unsigned int> it2;

                        std::set_intersection(finset.begin(),
                                              finset.end(),
                                              stateset.begin(),
                                              stateset.end(),
                                              std::inserter(it1, it1.begin()));

                        std::set_intersection(infset.begin(),
                                              infset.end(),
                                              stateset.begin(),
                                              stateset.end(),
                                              std::inserter(it2, it2.begin()));

                        // std::cout << "print it1" << std::endl;
                        // for (auto i : it1)
                        // {
                                // std::cout << i << std::endl;
                        // }
                        if (!it1.empty()){
                                statefinset.push_back(s);
                        } 
                        else if (!it2.empty()){
                                stateinfset.push_back(s);
                        }
                }
                fin_inf_tuple fin_inf{ statefinset, stateinfset };
                fin_inf_vec.push_back(fin_inf);
                
        }
        return fin_inf_vec;
}
#endif
