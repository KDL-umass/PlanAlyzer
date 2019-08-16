module Ast = Po_ast
module Syntax = Po_syntax

let ast_equal assert_bool is should_be = 
  let open Syntax in 
  let open Printf in 
  let rec nodes_equal is should_be = match is, should_be with   
    | Seq (h1::t1), Seq (h2::t2) -> 
      nodes_equal h1 h2; nodes_equal (Seq t1) (Seq t2)
    | Return g1, Return g2
    | Guard g1, Guard g2 -> bexprs_equal g1 g2 
    | Cond ((h11, h12)::t1), Cond ((h21, h22)::t2) -> 
      nodes_equal h11 h21; nodes_equal h12 h22;
      nodes_equal (Cond t1) (Cond t2)
    | Skip _, Skip _ -> ()
    | Expr e1, Expr e2 -> exprs_equal e1 e2 
    | Assignment (o1, s1, i1, e1), Assignment (o2, s2, i2, e2) ->
      assert_bool 
        (sprintf "Origins for assignment nodes (%s_%d, %s_%d) differ."
          s1 i1 s2 i2)
        (o1 = o2);
      assert_bool 
        (sprintf "Names for assignment nodes (%s_%d, %s_%d) differ."
          s1 i1 s2 i2)
        (s1 = s2 && i1 = i2);
      exprs_equal e1 e2
    | _, _ -> assert_bool (sprintf "Nodes don't match:\n%s\n\tvs.\n%s" 
      (Ast.Format.ast_string_of_program (Program is))
      (Ast.Format.ast_string_of_program (Program should_be)))
      (is = should_be) 
  and exprs_equal is should_be = 
    let msg = sprintf "expressions not equal:\n%s vs.\n%s" 
      (Ast.Format.ast_string_of_expr is)
      (Ast.Format.ast_string_of_expr should_be) in 
    match is, should_be with 
      | Aexpr e1, Aexpr e2 -> aexprs_equal e1 e2 
      | Bexpr e1, Bexpr e2 -> bexprs_equal e1 e2 
      | Cexpr e1, Cexpr e2 -> cexprs_equal e1 e2 
      | Sexpr e1, Sexpr e2 -> sexprs_equal e1 e2 
      | CustomExpr (name1, kvlist1, rand_info1), 
        CustomExpr (name2, kvlist2, rand_info2) ->
        assert_bool (sprintf 
          "custom expressions have different names: %s vs. %s" name1 name2)
          (name1 = name2);
        assert_bool (sprintf "%s has different rand_info: %s vs. %s"
          name1 
          (Ast.Format.ast_string_of_rand rand_info1)
          (Ast.Format.ast_string_of_rand rand_info2)) 
          (rand_info1 = rand_info2);
        kvlists_equal kvlist1 kvlist2
      | Coalesce (a1, d1), Coalesce (a2, d2) ->
        exprs_equal a1 a2; exprs_equal d1 d2
      | Iexpr (b1, i1), Iexpr (b2, i2) ->
        cexprs_equal b1 b2; exprs_equal i1 i2
      | RandomVar (w1, c1, u1, s1), RandomVar (w2, c2, u2, s2) ->
        cexprs_equal w1 w2; cexprs_equal c1 c2; uexprs_equal u1 u2;
        assert_bool msg (s1 = s2)      
      | _, _ -> assert_bool msg (is = should_be)
  and aexprs_equal is should_be = 
    let msg = sprintf "Numeric expressions not equal: \n\t%s\nvs.\n\t%s" 
      (Ast.Format.ast_string_of_expr (Aexpr is))
      (Ast.Format.ast_string_of_expr (Aexpr should_be)) in 
    assert_bool msg (is = should_be)
  and bexprs_equal is should_be = 
    let msg = sprintf "Boolean expressions not equal:\n\t%s\nvs.\n\t%s" 
      (Ast.Format.ast_string_of_expr (Bexpr is))
      (Ast.Format.ast_string_of_expr (Bexpr should_be)) in 
    assert_bool msg (is = should_be)
  and cexprs_equal is should_be = 
    let msg = sprintf "Container expressions not equal:\n\t%s\nvs.\n\t%s" 
      (Ast.Format.ast_string_of_expr (Cexpr is))
      (Ast.Format.ast_string_of_expr (Cexpr should_be)) in 
    assert_bool msg (is = should_be)
  and sexprs_equal is should_be = 
    let msg = sprintf "String expressions not equal:\n\t%s\nvs.\n\t%s" 
      (Ast.Format.ast_string_of_expr (Sexpr is))
      (Ast.Format.ast_string_of_expr (Sexpr should_be)) in 
    assert_bool msg (is = should_be)
  and uexprs_equal is should_be = 
    let msg = "Unit expressions not equal" in
    assert_bool msg (is = should_be)
  and kvlists_equal is should_be = ()
  in 
  match is, should_be with 
  | Program p1, Program p2 -> nodes_equal p1 p2 

let print_ast (p : Syntax.program) : unit =
  Printf.printf "\n%s\n" (Ast.Format.ast_string_of_program p)

let make_program2 execfn makeprogfn cfg p = 
  execfn p
  |> Yojson.Basic.from_string
  |> makeprogfn cfg 

let print_program p = 
  Po_format.string_of_program ~show_index:true p
  |> Printf.printf "\n%s\n"

let default_annot = "{userid : {card : \"high\", domain : \"number\"}}"

let prefix = "^fvid"
            
let p1 = "foo = 10;
  bar = foo * 9;
  baz = 30;
  return (baz * foo < bar);"

let p2 = "weights = [10, 0.4];
  choices = [\"asdf\", true];
  foo = weightedChoice(weights=weights, choices=choices, unit=userid);"

let p3 = "foo = 10;
  if (asdf) {
    foo = foo * 20;
  }
  bar = foo * foo;"

let p4 = "foo = 10 % 9;
  bar = ['a', 'b', 'c'][1];
  if (bar == 'a' || true) {
    return false;
  }"

let p5 = "foo = fn(arg1=a[b]);"
let p6 = "foo = fn(arg1=a[b], arg2=fooid) + 10;"
let p7 = "foo = a[b % length(a)][c][d];"

let p8 = "if (asdf && (a == b)) {
    return false;
 }
 return true;" 

let p9 = "if (a == 0 && b == 0) {
    if (length(c) > 1) {
        return true;
    } else if (fn(arg1=42)) {
        return false;
    } else {
        return true;
    }
 }
 " 

let causal_suff_1 = "if (extFn(userid=userid)) { 
    foo = bernoulliTrial(p=0.2, unit=userid);
    return true;
  }
  return false;"

let causal_suff_2 = "if (getUserCountry(userid=userid) == \"US\") {
  foo = bernoulliTrial(p=0.2, unit=userid);
  return true;
}
return false;
"

let reset_exp = "foo=bernoulliTrial(p=0.1, unit=(userid * 2));"

let p10 = "weights=[[0.1, 0.2], [0.3, 0.4]];
choices=[[4, 3], [2, 1]];
foo=weightedChoice(
    weights=weights[bernoulliTrial(p=0.5, salt=\"bar\", unit=userid)],
    choices=choices[bernoulliTrial(p=0.6, salt=\"baz\", unit=userid)],
    unit=userid);
"

let p11 = "if (foo == \"a\") {
    return true;
    }"
    
let p12 = "abc = extRandFn(unit=someid);
if (abc == 1234) {
    foo = \"a\";
} else if (abc == 2345) {
    foo = \"b\";
} else if (abc == 3456) {
    foo = \"c\";
} else if (abc < 5000){
    foo = \"d\";
} else {
    foo = \"e\";
}"

let p13 = "banner = uniformChoice ( choices =[A, B], unit = userid );
button = uniformChoice ( choices =[C, D], unit = banner );"

let p14 = "bmn = \"Life , friends , is boring \";
tny = \"To strive , to seek , to find , and not to yield \";
atw = \" Nolite te bastardes carborundorum \";
rand_quot = uniformChoice ( choices =[ bmn , tny , atw ],
unit = time );
ads_market = externalPredicate ( userid = userid );
if ( ads_market ) {
secret_sauce = uniformChoice ( choices =[A, B, C],
unit = userid );
} else {
return false ;
}
record = bernoulliTrial (p=0.5 , unit = userid );
return record;"

let p15 ="if ( bernoulliTrial (p=0.5 , unit = userid , salt =\"asdf\")) {
foo = 10;
} else {
foo = 10;
}"

let p16 = "country = getUserCountry ( userid = userid );
if ( country == \"USA\") {
free_trade_ad = bernoulliTrial (p=0.8 , unit = userid );
return true ;
} else if ( country == \"Canada\") {
free_trade_ad = bernoulliTrial (p=0.5 , unit = userid );
return false ;
} else if ( country == \"Mexico\") {
free_trade_ad = bernoulliTrial (p=0.7 , unit = userid );
return true ;
} else {
return false ;
}"

let p16b = "country = getUserCountry ( userid = userid );
if ( country == \"USA\") {
  free_trade_ad = bernoulliTrial (p=0.8 , unit = userid );
} else if ( country == \"Canada\") {
  free_trade_ad = bernoulliTrial (p=0.5 , unit = userid );
} else if ( country == \"Mexico\") {
  free_trade_ad = bernoulliTrial (p=0.7 , unit = userid );
} else {
  return false;
}
return true;"

let p17 = "country = getUserCountry ( userid = userid );
free_trade_ad = bernoulliTrial (p=0.5 , unit = userid );
if ( country == \"USA\") {
ad_lang = \"English\";
return true ;
} else if ( country == \"Canada\") {
ad_lang = uniformChoice ( choices =[\"English\", \"French\"],
unit = userid );
return false ;
} else if ( country == \"Mexico\") {
ad_lang = \"Spanish\";
return true ;
} else {
return false ;
}"

let p18 ="country = getUserCountry(userid=userid);
banner = uniformChoice(choices=[bannerA, bannerB], unit=userid);
randomSegment = getRandomSegment(userid=userid);
if (randomSegment < 1000) { 
    text = \"FOO\";
} else if (randomSegment == 1001) {
      if (country == \"Canada\") {
        text = \"Le BAR\";
      } else { 
        text = \"BAR\";
      }
} else {
      text = \"default text\";
}"

let p19 = "foo = uniformChoice(choices=[0,1,2], unit=userid); 
if (foo) { bar = \"a\"; } else { bar = \"b\"; }"

let p20 = "foo = bernoulliTrial(p=1/3, unit=userid);
if (a) {
    bar = 20;
} else {
    bar = \"asdf\";
}
"

let p21 = p20 ^ "bar = bar * 2;"

let p22 = "is_enabled = 0;
some_threshold_ms = 1000;
in_whitelist = externalRandomPredicate(ep=\"some_predicate\", unit=userid);

if(in_whitelist) {
  is_enabled = 1;
  some_threshold_ms = 0;

}
in_experiment = is_enabled;
"

let p23 = "if((1234 == userid)) {
  is_enabled = 1;
  threshold_ms = 10000;
  in_experiment = 1;
  log = [\"in_experiment\", \"is_enabled\", \"threshold_ms\"];
}
return in_experiment;
"

let p24 = "in_whitelist = 0;
whitelist_users = @{ 1234 : 1 };
in_whitelist = (userid && whitelist_users[userid]);
if (in_whitelist) {
    # do something
}"

let p25 = "title = uniformChoice(choices=[], unit=userid, salt=\"title\");"

let p26 = "foo1 = ((a + (-1 * b)) + 1);
foo2 = ((a + (-1 * b)) + 1);
foo3 = a + b + 1;
foo = ((a + (-1 * b)) + 1);"

let p27 = "in_experiment = bernoulliTrial(p=1, unit=userid);
threshold = randomFloat(max=-123, min=-987, unit=userid);
range = randomFloat(max=-123, min=-987, unit=userid);
minPenalty = randomFloat(max=-123, min=-987, unit=userid);
maxPenalty = randomFloat(max=-123, min=-987,  unit=userid);
return in_experiment;"

let p28 = "policy = bernoulliTrial(p=0.1, unit=userid);
context = getContext(userid=userid);
if (policy) {
    action = someTimeVaryingRandomAction(context=context, scenario=1);
} else {
    action = someTimeVaryingRandomAction(context=context, scenario=2);
}"

let p29 = "
a = 0;
if (!bernoulliTrial(p=0.5, unit=userid, salt=\"asdf\")) {} else {}
"

let p30 = "hide_feature = bernoulliTrial(p=0, unit=userid);
show_feature = bernoulliTrial(p=0, unit=userid);
hide_default = bernoulliTrial(p=0, unit=userid);"

let p31 = "if (foo) { 
    bar = baz[\"a\"];
} else {
    bar = 1;
}"

let p32 = "if (some_number) { foo = 1; } else { foo = 0; }"

let icse_example = "dynamic_policy = bernoulliTrial(p=0.3, unit=userid);
context = getContext(deviceid=deviceid, userid=userid);
emerging_market = (country == 'IN') || (country == 'BR');
established_market = (country == 'US') || (country == 'CA');
if(dynamic_policy) {
    weights = getBanditWeights(context=context, userid=userid);
    choices = getBanditChoices(context=context, userid=userid);
    max_bitrate = weightedChoice(choices=choices, weights=weights,
                                 unit=userid);
} else {
    if (emerging_market) {
      max_bitrate = weightedChoice(choices=[400, 750],
                                     weights=[0.9, 0.1], unit=userid);
    } else if (established_market) {
      max_bitrate = weightedChoice(choices=[400, 750],
                                     weights=[0.5, 0.5], unit=userid);
    } else {
      max_bitrate = 400;
    }
}"

let phi_test = "skip_logging = false;
enabled = false;

if((externalPredicate(userid=userid, ep=\"asdf\") || 
   !(externalPredicate(userid=userid, ep=\"fdsa\")))) {
  skip_logging = true;
} else {
  launched = bernoulliTrial(p=4/5, unit=userid);
  if(launched) {
      enabled = true;
      skip_logging = true;
  } else {
      enabled = bernoulliTrial(p=0.5, unit=userid);
  }
}

use_in_flyout = enabled;

if(skip_logging) {
  return false;
}" 

let scope_test = "targeted = externalPredicate(ep=\"asdf\", userid=userid);
  enabled = false;
  score = 0;
  median_score = 2345/5432;
  
  untargeted = bernoulliTrial(p=1/10, unit=userid);
  
  if(untargeted) {
    targeted = false;
    enabled = bernoulliTrial(p=4/5, unit=userid);
      
    if(enabled) {
      score = median_score;  
    }
  } else {

    if(targeted) {
      enabled = bernoulliTrial(p=4/5, unit=userid);
          
      if(enabled) {
        has_normal_score = bernoulliTrial(p=1/2, unit=userid);
              
        if(has_normal_score) {
          score = foo(userid=userid);
        } else {
          score = median_score;
        }
      }
  
    } else {
        return false;
    }
  }"
  
let inf_test = "foo = -1;
context = someExternalFn(userid=userid);
all_configs = @{\"a\" : 2, \"b\" : 3};
config = all_configs[context[\"asdf\"]];
if (!config) {
  return true;
}
foo = config;"

let within_subjects_1 = "foo = bernoulliTrial(p=0.5, unit=[userid, deviceid]);"

let within_subjects_2 = 
  "foo = bernoulliTrial(p=0.5, unit=[userid, deviceid]);
  if (foo) {
    bar = 10;
  } else { 
    bar = 20;
  }"

let within_subjects_3 = 
  "foo = bernoulliTrial(p=0.5, unit=userid);
  bar = bernoulliTrial(p=0.5, unit=deviceid);"

let test_data_flow = 
  "unit=userid % 10;
  foo = bernoulliTrial(p=0.5, unit=unit);"