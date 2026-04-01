#include <bits/stdc++.h>
using namespace std;

struct Term {
    long long a; // coefficient (can be negative)
    int b, c, d; // exponents: x^b sin^c cos^d
};

struct Poly {
    vector<Term> t;

    static bool same_kind(const Term &x, const Term &y){
        return x.b==y.b && x.c==y.c && x.d==y.d;
    }

    void simplify(){
        // combine like terms
        vector<Term> v;
        v.reserve(t.size());
        // use map key (b,c,d) -> sum a
        sort(t.begin(), t.end(), [](const Term &x, const Term &y){
            if (x.b!=y.b) return x.b>y.b; // sort desc to be stable later
            if (x.c!=y.c) return x.c>y.c;
            if (x.d!=y.d) return x.d>y.d;
            // keep order
            if (x.a!=y.a) return x.a>y.a; // arbitrary
            return false;
        });
        for (auto &e: t){
            if (!v.empty() && same_kind(v.back(), e)){
                v.back().a += e.a;
            }else{
                v.push_back(e);
            }
        }
        // remove zeros
        vector<Term> u;
        u.reserve(v.size());
        for (auto &e: v){
            if (e.a!=0) u.push_back(e);
        }
        // sort by keys desc as required
        sort(u.begin(), u.end(), [](const Term &x, const Term &y){
            if (x.b!=y.b) return x.b>y.b;
            if (x.c!=y.c) return x.c>y.c;
            if (x.d!=y.d) return x.d>y.d;
            // for consistent order: constants last if same keys already
            return x.a>y.a;
        });
        t.swap(u);
    }

    static Poly constant(long long k){
        Poly p; p.t.push_back({k,0,0,0}); return p;
    }

    Poly operator+(const Poly &o) const{
        Poly r; r.t.reserve(t.size()+o.t.size());
        r.t.insert(r.t.end(), t.begin(), t.end());
        r.t.insert(r.t.end(), o.t.begin(), o.t.end());
        r.simplify();
        return r;
    }
    Poly operator-(const Poly &o) const{
        Poly r; r.t.reserve(t.size()+o.t.size());
        r.t.insert(r.t.end(), t.begin(), t.end());
        for (auto e: o.t){ auto x=e; x.a = -x.a; r.t.push_back(x);}        
        r.simplify();
        return r;
    }
    Poly operator*(const Poly &o) const{
        Poly r; r.t.reserve((size_t)max<size_t>(1,t.size())*max<size_t>(1,o.t.size()));
        for (auto &x: t){
            for (auto &y: o.t){
                Term z; z.a = x.a * y.a;
                z.b = x.b + y.b;
                z.c = x.c + y.c;
                z.d = x.d + y.d;
                r.t.push_back(z);
            }
        }
        // handle case when one is empty (should not happen), keep empty means 0
        r.simplify();
        return r;
    }
    Poly derivate() const{
        Poly r;
        for (auto &x: t){
            // derivative with respect to x^b
            if (x.b>0){
                Term z = x; z.a = z.a * x.b; z.b = x.b-1; r.t.push_back(z);
            }
            // derivative of sin^c x part: n*sin^{n-1}x * cos x
            if (x.c>0){
                Term z = x; z.a = z.a * x.c; z.c = x.c-1; z.d = x.d+1; r.t.push_back(z);
            }
            // derivative of cos^d x part: -n * sin x * cos^{n-1} x
            if (x.d>0){
                Term z = x; z.a = z.a * (-x.d); z.d = x.d-1; z.c = x.c+1; r.t.push_back(z);
            }
        }
        r.simplify();
        return r;
    }

    bool is_one() const{ // equal to 1
        return t.size()==1 && t[0].a==1 && t[0].b==0 && t[0].c==0 && t[0].d==0;
    }
    bool is_zero() const{
        return t.empty();
    }

    string to_string_inner() const{
        if (t.empty()) return string("0");
        string out;
        for (size_t i=0;i<t.size();++i){
            const Term &e = t[i];
            long long a = e.a;
            bool neg = a<0; long long aa = neg? -a : a;
            // sign
            if (i==0){
                if (neg) out.push_back('-');
            }else{
                out.push_back(neg?'-':'+');
            }
            bool is_const = (e.b==0 && e.c==0 && e.d==0);
            if (is_const){
                out += std::to_string(aa);
                continue;
            }
            if (aa!=1){
                out += std::to_string(aa);
            }
            // x part
            if (e.b>0){
                out += "x";
                if (e.b>1){ out += "^" + std::to_string(e.b); }
            }
            // sin part
            if (e.c>0){
                out += "sin";
                if (e.c>1){ out += "^" + std::to_string(e.c); }
                out += "x";
            }
            // cos part
            if (e.d>0){
                out += "cos";
                if (e.d>1){ out += "^" + std::to_string(e.d); }
                out += "x";
            }
        }
        return out;
    }
};

struct Frac{
    Poly p, q; // p/q
    Frac(){}
    Frac(long long k){ p = Poly::constant(k); q = Poly::constant(1); }
    Frac(const Poly &pp, const Poly &qq): p(pp), q(qq){}
};

static Frac add(const Frac &x, const Frac &y){
    return Frac(x.p * y.q + y.p * x.q, x.q * y.q);
}
static Frac subf(const Frac &x, const Frac &y){
    return Frac(x.p * y.q - y.p * x.q, x.q * y.q);
}
static Frac mul(const Frac &x, const Frac &y){
    return Frac(x.p * y.p, x.q * y.q);
}
static Frac divf(const Frac &x, const Frac &y){
    return Frac(x.p * y.q, x.q * y.p);
}
static Frac derivate(const Frac &f){
    // (p/q)' = (p' * q - q' * p) / (q*q)
    Poly pp = f.p.derivate();
    Poly qq = f.q.derivate();
    Poly num = pp * f.q - qq * f.p;
    Poly den = f.q * f.q;
    return Frac(num, den);
}

static string print_frac(const Frac &f){
    // handle zero numerator
    Poly pn = f.p; Poly qn = f.q; pn.simplify(); qn.simplify();
    if (pn.t.empty()) return string("0");
    if (qn.is_one()){
        return pn.to_string_inner();
    }
    string s1 = pn.to_string_inner();
    string s2 = qn.to_string_inner();
    // remove parentheses if single term
    bool p_mul = pn.t.size()>1;
    bool q_mul = qn.t.size()>1;
    string out;
    if (p_mul) out.push_back('(');
    out += s1;
    if (p_mul) out.push_back(')');
    out.push_back('/');
    if (q_mul) out.push_back('(');
    out += s2;
    if (q_mul) out.push_back(')');
    return out;
}

struct Parser{
    const string &s;
    int n; int i;
    Parser(const string &str): s(str), n((int)str.size()), i(0) {}

    bool end() const { return i>=n; }
    char peek() const { return i<n? s[i] : '\0'; }
    char get(){ return i<n? s[i++] : '\0'; }

    bool is_boundary(char c){
        return c=='+'||c=='-'||c=='*'||c=='/'||c==')' || c=='\0';
    }

    Frac parse(){ return parseExpr(); }

    Frac parseExpr(){
        Frac v = parseTerm();
        while (!end()){
            char c = peek();
            if (c=='+'){ get(); Frac r = parseTerm(); v = add(v, r); }
            else if (c=='-'){ get(); Frac r = parseTerm(); v = subf(v, r); }
            else break;
        }
        return v;
    }
    Frac parseTerm(){
        Frac v = parseUnary();
        while (!end()){
            char c = peek();
            if (c=='*'){ get(); Frac r = parseUnary(); v = mul(v, r); }
            else if (c=='/'){ get(); Frac r = parseUnary(); v = divf(v, r); }
            else break;
        }
        return v;
    }
    Frac parseUnary(){
        if (peek()=='+'){ get(); return parseUnary(); }
        if (peek()=='-'){ get(); Frac r = parseUnary(); return mul(Frac(-1), r); }
        return parsePrimary();
    }
    Frac parsePrimary(){
        if (peek()=='('){
            get();
            Frac v = parseExpr();
            if (peek()==')') get();
            return v;
        }
        return parseLiteral();
    }
    bool starts_literal(){
        if (end()) return false;
        if (isdigit(peek())) return true;
        if (peek()=='x') return true;
        if (peek()=='s' || peek()=='c') return true; // sin/cos
        return false;
    }
    Frac parseLiteral(){
        // parse a product-like literal with no explicit '*' inside
        Poly p; Term cur{1,0,0,0};
        bool any=false;
        // optional leading integer coefficient
        if (isdigit(peek())){
            long long val=0; while (!end() && isdigit(peek())){ val = val*10 + (get()-'0'); }
            cur.a = val; any=true;
        }
        while (!end()){
            if (is_boundary(peek())) break;
            if (peek()=='x'){
                get(); // consume 'x'
                int exp=1;
                if (peek()=='^'){
                    get(); int e=0; bool has=false; while (!end() && isdigit(peek())){ has=true; e=e*10+(get()-'0'); }
                    if (has) exp=e; else exp=0; // should not happen
                }
                cur.b += exp; any=true;
                continue;
            }
            if (peek()=='s'){
                // expect sin
                if (i+2<n && s.substr(i,3)=="sin"){
                    i+=3; int exp=1;
                    if (peek()=='^'){
                        get(); int e=0; bool has=false; while (!end() && isdigit(peek())){ has=true; e=e*10+(get()-'0'); }
                        if (has) exp=e; else exp=0;
                    }
                    // expect 'x'
                    if (peek()=='x') get();
                    cur.c += exp; any=true; continue;
                }
            }
            if (peek()=='c'){
                // expect cos
                if (i+2<n && s.substr(i,3)=="cos"){
                    i+=3; int exp=1;
                    if (peek()=='^'){
                        get(); int e=0; bool has=false; while (!end() && isdigit(peek())){ has=true; e=e*10+(get()-'0'); }
                        if (has) exp=e; else exp=0;
                    }
                    if (peek()=='x') get();
                    cur.d += exp; any=true; continue;
                }
            }
            // unknown sequence; break to avoid infinite loop
            break;
        }
        if (!any){
            // if nothing parsed, treat as 1
            cur.a = 1; any=true;
        }
        Poly pp; pp.t.push_back(cur); pp.simplify();
        Poly qq = Poly::constant(1);
        return Frac(pp, qq);
    }
};

int main(){
    ios::sync_with_stdio(false);
    cin.tie(nullptr);
    string str; if(!(cin>>str)) return 0;
    Parser parser(str);
    Frac g = parser.parse();
    // simplify polys (already mostly simplified via ops)
    g.p.simplify(); g.q.simplify();
    Frac h = derivate(g);
    // outputs
    cout << print_frac(g) << '\n';
    cout << print_frac(h) << '\n';
    return 0;
}

