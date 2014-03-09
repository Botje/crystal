$(function() {

	String.prototype.repeat = String.prototype.repeat || function(num) {
    return new Array(isNaN(num)? 1 : ++num).join(this);
	}

	var output;

	function Empty() {
	}

	Empty.prototype.render = function(out) {
	}

	function Line() {
	}

	Line.prototype.render = function(out) {
		out.append("\n");
	}

	function Text(t) {
		this.text = t;
	}
	
	Text.prototype.render = function(out) {
		out.append(this.text);
	}

	function Ann(a) {
		this.a = a;
	}

	Ann.prototype = new Text();
	Ann.prototype.constructor = Ann;
	Ann.prototype.render = function(out) {
		var div = $("<span class='label' />");
		var lab = this.a.label;
		lab = lab.replace(/^LSource /,"");
		lab = lab.replace(/"/,"");
		lab = lab.replace(/"/,"");
		lab = lab.replace(/^LPrim /,"");
		this.a.label = lab;
		div.text(lab);
		div.attr('title', JSON.stringify(this.a, null, " "));
		div.tooltip();
		out.append(div);
	}

	function Cons(l, r) {
		this.l = l;
		this.r = r;
	}
	
	Cons.prototype.render = function(out) {
		this.l.render(out);
		this.r.render(out);
	}

	function Nest(n, d) {
		this.n = n;
		this.d = d;
	}

	Nest.prototype.render = function(out) {
		if (this.d instanceof Empty) {
			this.d.render(out);
		} else if (this.d instanceof Line) {
			this.d.render(out);
			out.append(" ".repeat(this.n));
		} else if (this.d instanceof Text) {
			this.d.render(out);
		} else if (this.d instanceof Cons) {
			new Cons(nest(this.n, this.d.l), nest(this.n, this.d.r)).render(out);
		} else if (this.d instanceof Nest) {
			new Nest(this.n + this.d.n, this.d.d).render(out);
		}
	}

	function empty() {
		return new Empty();
	}

	function text(t) {
		return new Text(t);
	}

	function line() {
		return new Line();
	}

	function cons() {
		var params = Array.prototype.slice.call(arguments);
		var doc = params.pop();
		while (params.length)
			doc = new Cons(params.pop(), doc);
		return doc;
	}

	function consS() {
		var params = Array.prototype.slice.call(arguments);
		var doc = params.pop();
		while (params.length)
			doc = cons(params.pop(), text(" "), doc);
		return doc;
	}

	function nest(n, d) {
		return new Nest(n, d);
	}

	function indent(n, d) {
		return nest(n, cons(line(), d));
	}

	function parens(d) {
		return cons(text("("), d, text(")"));
	}

	function ann(a) {
		return new Ann(a);
	}

	function pretty(tree) {
		return cons(ann(tree.ann), prettyPrint(tree));
	}

	function prettyPrint(tree) {
		switch (tree.type) {
			case "LetExpression": 
				return parens(cons(text(tree.kw), text(" "),
				       parens(cons(text(tree.head[0].id), text(" "), pretty(tree.head[0].init))),
				       indent(2, pretty(tree.body))
				       ));
				break;

			case "CallExpression":
				var temp = tree.arguments.map(pretty);
				temp.unshift(pretty(tree.callee));
				return parens(consS.apply(null, temp));

			case "FunctionExpression":
				return parens(consS(text("lambda"),
				                    parens(consS.apply(null, tree.params.map(text))),
				                    indent(2, pretty(tree.body))))
				return undefined;

			case "SequenceExpression":
				var exprs = tree.expressions.map(pretty);
				exprs = exprs.map(function(x) { return cons(x, line()); });
				return parens(cons(text("begin"), indent(2, cons.apply(null, exprs))));

			case "ConditionalExpression":
				return parens(consS(text("if"), pretty(tree.test), indent(2, pretty(tree.consequent)), indent(2, pretty(tree.alternative))));
			case "Identifier":
				return text(tree.name);

			case "Literal":
				if (tree.value == "True") 
					return text("#t");
				if (tree.value == "False") 
					return text("#f");
				if (tree.value == "#<void>") 
					return text("#&lt;void>");
				return text(tree.value);

			default:
				return text(tree.type);
		}
	}

	$("#pretty-button").click(function(){
		var input = $("#rawjson").val();
		input = input.replace("<![CDATA[","");
	  input = input.replace("]]>", "");
		tree = JSON.parse(input);

		output = $("#pretty-output").first();
		output.empty();
		pretty(tree).render(output);
	});
});
