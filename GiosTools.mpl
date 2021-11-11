restart: # gtsimplify(%,pochhammer,showall)
#savelibname := "D:\\Helium\\Coding\\GiosTools\\GiosTools.mla":
#savelibname := "/home/giogina/Desktop/Helium/Coding/GiosTools/GiosTools.mla":
savelibname := "./GiosTools.mla":

#LibraryTools[ShowContents]("D:\\Helium\\Coding\\GiosTools"):

GiosTools := module()
  description "Some procedures dealing with recursions, power series, and variables suitable for Helium.":
  option package:
  export getTeX,trimpoch,trimfac,trimpochfac,`&>`,showcoord,L,HH,Dchange,Collect,invertpolynomial,compare,gsimplify,gchange,gsplit,ratplot,IdSeq,IdSer,multiangle,RecRel,expandsqrta,combinesqrta,Expand,summap,symplify,VOP,VOP0,SERR,opm2,opm1,op0,op1,op2,posfactor,combinepowers,assumecoords,assumeinds,app2seq,getseq,setseq,resetseq,nextcoeff:
  local ElementaryConversions,Maple2TeX,coordtools,gFktCoeffs,ModuleLoad,getser,invertpolytools,IdSeqMod,hypconvert,getshifts,hyper2sum,RecRelinner,binomexpand:

  ModuleLoad:=proc()
     global `type/coordsys`, `convert/poch`,`convert/pochfac`, `convert/hyper`, `convert/sum`, `type/halfint`, `type/mod1`, `type/id`, `type/divisible`:

    `type/coordsys`:=proc(cc)
      local csys:=true:
      try
        coordtools:-getcsys(cc):
      catch: csys:=false: end try:
      return csys:
    end proc:

    `convert/poch`:=proc(expr)
      return ElementaryConversions:-gtconvert(expr,poch):
    end proc:

    `convert/pochfac`:=proc(expr)
      return ElementaryConversions:-gtconvert(expr,pochfac):
    end proc:
    
    `convert/hyper`:=proc(expr)
      return hypconvert(expr):
    end proc:

    `convert/sum`:=proc(expr,varinp:=auto,indinp:=[],{differentialorder:=4,dir:=`default`,makereal:=true,method:=`default`,recurrence:=false})
      local usedids, inds, backupinds:=[i, j, k, n, m, l, seq(op([i||ii, j||ii, k||ii, n||ii, m||ii]),ii=1..ceil(nops(indets(expr,function))/5+1))],opts,var:
      opts:=map(zz->convert(lhs(zz),name)=rhs(zz),["differentialorder"=differentialorder,"dir"=dir,"makereal"=makereal,"method"=method,"recurrence"=recurrence]);

                                                                                        # Determine index order:
      usedids:=indets(expr,name):                                                       # Names that are already in use
      inds:=map(zz->`if`(zz in usedids,NULL,zz),indinp);                                # Take out used indices from original input
      backupinds:=map(zz->`if`(zz in usedids union {op(inds)},NULL,zz),backupinds);     # Take out used & given indices from backup
      if nops(indinp)>0 and nops(inds)=0 then
        WARNING(`Given index is already in use, changing index...`);
      end if;
      inds:=[op(inds),op(backupinds)];                                                  # Merge remaining given & backup indices

      if not varinp=auto then var:=varinp:
      elif nops(indets(expr,name))=1 then var:=op(1,indets(expr,name));
      end if:

      return hyper2sum(expr,inds,varinp,opts):                                          # Call hyper2sum with predetermined order of indices to be used.
    end proc:

    `type/halfint`:=proc(cc)
        if is(2*cc,integer) and not is(cc,integer) then
          return true;
        else
          return false;
        end if:
    end proc:

    `type/mod1`:=proc(cc,ff)
        if is(cc,rational) and cc-floor(cc)=ff then return true;
        else return false;
        end if;
    end proc:

    `type/id`:=proc(cc,ff)
        if cc=ff then return true;
        else return false;
        end if;
    end proc:

    `type/divisible`:=proc(cc,ff)
        return is(denom(factor(cc/ff)),constant);
    end proc:


    alias(idseq=IdSeq);
    alias(idser=IdSer);
    alias(gettex=getTeX);
    #alias(poch=pochhammer); # not very pretty, as it leaves the 'poch' in italics. Other way around just deactivates pochhammer.
    #alias(F=hypergeom);

  end proc:


    ##################################################################################
    ##################################################################################
    ## convert for conversions between Gamma, pochhammer, factorials and binomials. ##
    ##################################################################################
    ##################################################################################

  ElementaryConversions:=module()
    description "Elementary Conversions between pochhammer, GAMMA, binomials and factorials.":
    local isposint, Gamma2pochhammer, Gamma2factorial, Gamma2pochfac, pochhammer2factorial, pochhammer2pochfac, pochhammer2GAMMA, binomial2factorial, binomial2pochfac, binomial2pochhammer, binomial2GAMMA, Gamma2GAMMA, factorial2factorial, pochhammer2pochhammer, factorial2GAMMA, factorial2pochfac,factorial2pochhammer,isnonnegint,Gamma2poch,factorial2poch,binomial2poch,pochhammer2poch,doublefactorial2poch,doublefactorial2pochfac:
    export gtconvert,trimpochinner,trimfacinner:

    isnonnegint:=proc(expr)
      return is(expr,nonnegint)  assuming op(map(zz->zz::posint,indets(expr,name) minus {dummy}));
    end proc:

    Gamma2poch := proc(expr)
      local pochk, pochn, ii, res:
      pochn:=remove(zz->not type(zz,numeric) and isnonnegint(zz),expr+dummy)-dummy:
      pochk:=expr-pochn:
      if evalb(pochn=0) then      res := pochhammer(1, pochk-1)      else      res := pochhammer(pochn, pochk)*GAMMA(pochn)    end if:
      if simplify(convert(res, GAMMA)-GAMMA(expr),GAMMA) = 0 then      return res     else      return GAMMA(expr)     end if
    end proc:

    Gamma2pochfac := proc (expr)
      if isnonnegint(expr) then      return factorial(expr-1)      else      return Gamma2poch(expr)     end if
    end proc:

    pochhammer2pochfac := proc (expr1, expr2)
      if type(expr1, numeric) and isnonnegint(expr1) then
        return factorial(expr1+expr2-1)/factorial(expr1-1) 
      else
        return pochhammer(expr1, expr2) 
      end if
    end proc:

    binomial2poch := proc (expr1, expr2)
      if isnonnegint(expr2) or coulditbe(expr2,nonnegint) then
        return pochhammer(-expr1, expr2)/(pochhammer(1, expr2)*simplify((-1)^expr2));
      else
        return binomial(expr1,expr2)
      end if:
    end proc:

    binomial2pochfac := proc (expr1, expr2)
      if isnonnegint(expr2) or coulditbe(expr2,nonnegint) then
        return pochhammer(-expr1, expr2)/(factorial(expr2)*simplify((-1)^expr2))
      else
        return binomial(expr1,expr2)
      end if:
    end proc:

    factorial2poch := proc (expr) return pochhammer(1,expr): end proc:
    pochhammer2poch := proc (expr1, expr2) return pochhammer(expr1, expr2) end proc:
    factorial2pochfac := proc (expr) return factorial(expr) end proc:

    doublefactorial2poch:=proc(expr)
      local pochn,pochk,res:
      eval(expr,map(zz->zz=1,indets(expr,name))):
      if not is(%,integer) then return doublefactorial(expr): end if:
      if is(%,odd) then
        pochn:=1/2:
      else
        pochn:=1:
      end if:
      pochk:=expr/2+1-pochn:
      res := 2^pochk*pochhammer(pochn, pochk):
      if eval(doublefactorial(expr)/res,map(zz->zz=1,indets(expr,name)))=1 then      return eval(res,pochhammer=trimpochinner)     else      return doublefactorial(expr)     end if;
    end proc:

    doublefactorial2pochfac:=proc(expr)
      return eval(doublefactorial2poch(expr),pochhammer=pochhammer2pochfac);
    end proc:

    trimpochinner := proc(expr1,expr2)  # turns pochhammer(a,b*n+c) into pochhammer(a+c,b*n), removing purely numerical terms from the second argument
      local pochk, pochn, ii, res:
      pochn:=remove(zz->not type(zz,numeric),expr2+dummy):
      pochk:=expr2-pochn:
      if pochk=0 then return pochhammer(expr1,expr2); end if:
      if evalb(pochn=0) then
        res := pochhammer(expr1,expr2)
      else
        res := pochhammer(expr1+pochn, pochk);
      end if:
      return rhs(gchange(pochhammer(expr1,expr2),res));
    end proc:

    trimfacinner := proc(expr)
      remove(zz->not type(zz,numeric),expr+dummy); # Purely numeric part of expr
      expr-%;                                      # Non-numeric rest
      if is(%%,negint) then
          return rhs(gchange(factorial(expr),(%)!/mul(%+%%+ii,ii=1..-%%)))
      else
        return expr!;
      end if;
    end proc:

    gtconvert:=proc(expr, convgoal)
      local ac:
      ac:=[GAMMA,poch,factorial,pochfac]:
      if ListTools:-Search(convgoal,ac)=0 then
        WARNING(cat("Only implemented conversions: ",seq(cat(op(ii,ac),", "),ii=1..nops(ac)-1),op(nops(ac),ac))):
        return expr:
      else
        eval(eval(subs({GAMMA = ElementaryConversions[Gamma2||convgoal],pochhammer = ElementaryConversions[pochhammer2||convgoal],
                binomial = ElementaryConversions[binomial2||convgoal],factorial = ElementaryConversions[factorial2||convgoal],
                doublefactorial = ElementaryConversions[doublefactorial2||convgoal]}, expr))
             ,pochhammer=trimpochinner):
        return `%`:
      end if:
    end proc:

    end module: # ElementaryConversions


    trimpoch := proc(expr)  # turns pochhammer(a,b*n+c) into pochhammer(a+c,b*n), removing purely numerical terms from the second argument
      return eval(expr,pochhammer=ElementaryConversions:-trimpochinner);
    end proc:

    trimfac := proc(expr)  # turns (n-j)! into n!/(n-j+1)/.../(n-1)
      return eval(expr,factorial=ElementaryConversions:-trimfacinner);
    end proc:

    trimpochfac := proc(expr)  # both of the above
      return trimpoch(trimfac(expr));
    end proc:
    

    ####################################################################################
    ####################################################################################
    ##                            Maple to LaTeX converter                            ##
    ####################################################################################
    ####################################################################################

    Maple2TeX:=module()
      export getstr, verbose:

      getstr:=proc(ff)
        local oo,sumlb,sumub,jj,gpn,gpd,gpe,da,dc,dv,dvs,newv,ii,gs,twoliners,greeks,si,js;
        twoliners:=[`diff`,`binomial`,`Sum`,`sum`,`Int`,`int`,`Fraction`]:
        greeks:=[alpha,beta,gamma,delta,epsilon,zeta,eta,pi,theta,iota,kappa,lambda,mu,nu,xi,pi,rho,sigma,tau,phi,chi,psi,omega]:
        oo:=op(0,ff);
        if verbose then print(oo,ff); end if;
        if(oo = `=`) then
          return cat(getstr(lhs(ff)),"=",getstr(rhs(ff)));

        elif(oo = `Sum` or oo = `sum`) then
          if (op(0,op(-1,ff))=`=`) then
            sumlb:=cat(" _{",convert(lhs(op(-1,ff))=op(1,rhs(op(-1,ff))),string),"}");
            sumub:=cat(" ^ {",convert(op(2,rhs(op(-1,ff))),string),"}");
            if sumub=" ^ {infinity}" then sumub:=" ^ {\\infty}": end if:
          else
            sumlb:="": sumub:="":
          end if:
          return cat("\\sum ",sumlb,sumub," ",getstr(op(1,ff))," ");  #{} removed: ," {",getstr(op(1,ff)),"}"

        elif(oo = `Int` or oo = `int`) then
          if (op(0,op(-1,ff))=`=`) then
            sumlb:=cat(" _{",getstr(op(1,rhs(op(-1,ff)))),"}");
            sumub:=cat(" ^ {",getstr(op(2,rhs(op(-1,ff)))),"}");
            if sumlb=" _{-{infinity}}" then sumlb:=" _{- \\infty}": end if:
            if sumub=" ^ {infinity}" then sumub:=" ^ {\\infty}": end if:
          else
            sumlb:="": sumub:="":
          end if:
          return cat("\\int ",sumlb,sumub," ",getstr(op(1,ff))," d ",convert(lhs(op(-1,ff)),string)); #{} removed: ...," {",getstr(op(1,ff)),"} d ",...

        elif (oo=`diff`) then
          da:=op(1,ff): # Term
          dc:=1: dv:=1:  # order of derivative, number of variables
          dvs[1,1]:=getstr(op(2,ff)):  # library of variables
          dvs[1,2]:=1:
          while op(0,da)=`diff` do
            newv:=true:  # trying to find variable in library
            for ii from 1 to dv do
              if getstr(dvs[ii,1])=getstr(op(2,da)) then
                dvs[ii,2]:=dvs[ii,2]+1:
                newv:=false:
              end if:
            end do:
            if newv then # new variable found
              dv:=dv+1:
              dvs[dv,1]:=getstr(op(2,da)):
              dvs[dv,2]:=1:
            end if:
            dc:=dc+1:
            da:=op(1,da):
          end do:
          if nops(da)>1 then  # partial derivative
            for ii from 1 to dv do
              if dvs[ii,2]>1 then
                dvs[ii,3]:=cat(" \\partial ",dvs[ii,1]," ^ ",dvs[ii,2]):
              else
                dvs[ii,3]:=cat(" \\partial ",dvs[ii,1]):
              end if:
            end do:
            if dc > 1 then
              return cat("{\\partial ^ ",dc," \\over ",seq(dvs[jj,3],jj=1..dv),"} ",getstr(da)," "): #{} removed: ...," \\over {",seq(dvs[jj,3],jj=1..dv),"}} ",...
            else
              return cat("{\\partial \\over ",seq(dvs[jj,3],jj=1..dv),"} ",getstr(da)," "):          #{} removed: ...\\over {",seq(dvs[jj,3],jj=1..dv),"}} ",...
            end if:
          else  # normal derivative
            if dc > 1 then
              return cat("{d ^ ",dc," \\over d",dvs[1,1]," ^ ",dc,"}",getstr(da)," "):               #{} removed
            else 
              return cat("{d \\over d",dvs[1,1],"}",getstr(da)," "):                                 #{} removed: ("{{d \\over {d",dvs[1,1],"}}",getstr(da),"}")
            end if:
          end if:

        elif (oo=`+`) then
          for jj from 2 to nops(ff) do
            js:=getstr(op(jj,ff));
            if verbose then print("In `+`: js=",js); end if;
            if(js[1]="-") then
              gs[jj]:=cat(" - ",js[2..-1]);
            else
              gs[jj]:=cat(" + ",js);
            end if:
          end do:
          si:=1:
          try
            si := sign(op(1,ff)):
          catch:
            try si := sign(op(1,op(1,ff)))=(-1): catch: end try:
          end try:
          if si=(-1) then
            if gs[2][1..3]=" + " then                                                       #If first summand is negative, move it to the end.
              return cat(seq(gs[kk],kk=2..nops(ff))," - ",getstr(-op(1,ff)))[4..10000]:
            else
              return cat(seq(gs[kk],kk=2..nops(ff))," - ",getstr(-op(1,ff))):
            end if:
          else
            return cat(getstr(op(1,ff)),seq(gs[kk],kk=2..nops(ff))):
          end if:

        elif (oo=`*`) then
          si:=1:
          try
            si := sign(op(1,ff)):
          catch:
            try si := sign(op(1,op(1,ff)))=(-1): catch: end try:
          end try:
          if si=(-1) then
            return cat("-",getstr(-ff)," "):                                           # removed {}: cat("-{",getstr(-ff),"}"):
          end if:
          gpn:="": gpd:="": gpe:="":  # Numerator, denominator, external factors
          for jj from 1 to nops(ff) do
           if op(0,op(jj,ff))=`+` or op(0,1/op(jj,ff))=`+` then
            js:=getstr(op(jj,ff));
            if (js[1..9]="{1 \\over ") and js[-1]="}" then
              gpd:=cat(gpd," \\cdot \\left(",js[10..-2],"\\right)");
            elif (js[1..8]="1 \\over ") then
              gpd:=cat(gpd," \\cdot \\left( ",js[9..-1],"\\right)");
            else
              gpn:=cat(gpn," \\cdot \\left(",getstr(op(jj,ff)),"\\right)");
            end if:
           else
            js:=getstr(op(jj,ff));
            if (js[1..9]="{1 \\over ")  and js[-1]="}" then
              gpd:=cat(gpd," \\cdot ",getstr(op(jj,ff))[10..-2]);
            elif (js[1..8]="1 \\over ") then
              gpd:=cat(gpd," \\cdot ",js[9..-1]);
            elif ListTools:-Search(op(0,op(jj,ff)),twoliners)>0 then
              gpe:=cat(gpe," \\cdot ",js):
            else
              gpn:=cat(gpn," \\cdot ",js):
            end if:
           end if:
          end do:

          if type(op(1,ff),integer) and cat(getstr(abs(op(1,ff)))," \\cdot ")=gpn[8..14+length(getstr(abs(op(1,ff))))] then   #Remove cdots after integers
            gpn:=cat("       ",getstr(abs(op(1,ff)))," ",gpn[15+length(getstr(abs(op(1,ff))))..10000]):
          end if:
          if type(1/op(1,ff),integer) and cat(getstr(1/abs(op(1,ff)))," \\cdot ")=gpd[8..14+length(getstr(1/abs(op(1,ff))))] then
            gpd:=cat("       ",getstr(1/abs(op(1,ff)))," ",gpd[15+length(getstr(1/abs(op(1,ff))))..10000]):
          end if:
          if verbose then print("In `*`: gpn, gpd, gpe = ",gpn,gpd,gpe); end if;
          if not gpd="" then
           if gpn="" then
            return cat("{1 \\over ",gpd[8..-1],"}",gpe):                      #{} removed:  cat("{1 \\over {",gpd[8..10000],"}}",gpe):
           else
            return cat("{",gpn[8..-1]," \\over ",gpd[8..-1],"}",gpe):         #{} removed:  cat("{{",gpn[8..10000],"} \\over {",gpd[8..10000],"}}",gpe):
           end if:
          else
            return cat(gpn[8..-1],gpe):
          end if:

        elif (oo=`^`) then
          if getstr(op(2,ff))[1]="-" then
            return cat("{1 \\over ", getstr(1/ff),"}"):       #{} removed: cat("{1 \\over {", getstr(1/ff),"}}"):
          elif op(2,ff)=1/2 then
            return cat("\\sqrt{",getstr(op(1,ff)),"}"):
          else
            if op(0,op(1,ff))=`+` or getstr(op(1,ff))[1]="-" then
              return cat("(",getstr(op(1,ff)),") ^ {",getstr(op(2,ff)),"}"):
            elif is(op(1,ff),atomic) or is(op(1,ff),function) then
              return cat(" ",getstr(op(1,ff)), " ^ {",getstr(op(2,ff)),"}"):
            else
              return cat("{",getstr(op(1,ff)),"} ^ {",getstr(op(2,ff)),"}"):
            end if:
          end if:

        elif (oo=`hypergeom` or oo=`Hypergeom`) then
          return cat("\\pFq{",nops(op(1,ff)),"}{",nops(op(2,ff)),
                     "}{",`if`(nops(op(1,ff))=0,"-",cat(op(map(zz->cat(getstr(zz),","),op(1,ff)[1..-2])),getstr(op(1,ff)[-1]))),
                     "}{",`if`(nops(op(2,ff))=0,"-",cat(op(map(zz->cat(getstr(zz),","),op(2,ff)[1..-2])),getstr(op(2,ff)[-1]))),
                     "}{{",getstr(op(3,ff)),"}}");

        elif (oo=`exp`) then
          return cat("\\mathbf{e} ^ {",getstr(op(1,ff)),"}"):
        elif (oo=`pochhammer`) then
          return cat("\\left( ",getstr(op(1,ff))," \\right) _ {",getstr(op(2,ff)),"}"):
        elif (oo=`binomial`) then
          return cat(" \\binom{{",getstr(op(1,ff)),"}}{{",getstr(op(2,ff)),"}}"):
        elif (oo=`factorial`) then
          if length(getstr(op(1,ff)))=1 then
            return cat(" ",getstr(op(1,ff)),"! "):
          else
            return cat(" (",getstr(op(1,ff)),")! "):
          end if:
        elif (oo=`GAMMA`) then
          return cat("\\Gamma \\left( ",getstr(op(1,ff))," \\right)"):
        elif oo=`floor` then
          return cat(" \\left \\lfloor{",getstr(op(1,ff)),"}\\right \\rfloor ");
        elif oo=`ceil` then
          return cat(" \\left \\lceil{",getstr(op(1,ff)),"}\\right \\rceil ");
        elif type(oo,procedure) and nops(ff)=1 then
          return cat("\\text{",convert(op(-2,ff),string),"} \\left( ",getstr(op(1,ff))," \\right) ");
        elif type(oo,procedure) and nops(ff)=2 then
          return cat(convert(op(-2,ff),string)," \\left( ",getstr(op(1,ff)),",",getstr(op(2,ff))," \\right) ");
        elif ListTools:-Search(op(1,ff),greeks)>0 and nops(ff)=1 then
          return cat("\\",op(1,ff));
        elif op(1,ff)=`Pi` and nops(ff)=1 then
          return cat("\\pi");  
        elif type(ff,indexed) then
          return cat(getstr(op(0,ff))," _ {",getstr(op(1,ff)),seq(cat(",",getstr(op(ii,ff))),ii=2..nops(ff)),"}"):
        elif (oo=`Fraction`) then
          if op(1,ff)=1 then
            return cat("{1 \\over ",getstr(1/ff),"}"):
          elif op(1,ff)=-1 then
            return cat("-{1 \\over ",getstr(-1/ff),"}"):
          else
            return cat("{",getstr(op(1,ff))," \\over ",getstr(op(2,ff)),"}"):
          end if:
        elif type(ff,function) and nops(ff)=1 then
          return cat(getstr(op(0,ff))," \\left( ",getstr(op(1,ff))," \\right) ");
        elif type(ff,function) and nops(ff)=2 then
          return cat(getstr(op(0,ff))," \\left( ",getstr(op(1,ff)),",",getstr(op(2,ff))," \\right) ");
       elif type(ff,function) and nops(ff)=3 then
          return cat(getstr(op(0,ff))," \\left( ",getstr(op(1,ff)),",",getstr(op(2,ff)),",",getstr(op(3,ff))," \\right) ");
        elif ff=r1 then return "r_{1}";
        elif ff=r2 then return "r_{2}";
        elif ff=r12 then return "r_{12}";
        elif ff=rz then return "r_{z}";
        elif ff=alpha then return "\\alpha "
        elif ff=beta then return "\\beta ";
        elif ff=gamma then return "\\gamma "
        elif ff=delta then return "\\delta "
        elif ff=epsilon then return "\\epsilon "
        elif ff=zeta then return "\\zeta "
        elif ff=eta then return "\\eta"
        elif ff=theta then return "\\theta "
        elif ff=iota then return "\\iota "
        elif ff=kappa then return "\\kappa "
        elif ff=lambda then return "\\lambda "
        elif ff=mu then return "\\mu "
        elif ff=nu then return "\\nu "
        elif ff=xi then return "\\xi "
        elif ff=omicron then return "\\omicron "
        elif ff=pi then return "\\pi "
        elif ff=rho then return "\\rho "
        elif ff=sigma then return "\\sigma "
        elif ff=tau then return "\\tau "
        elif ff=upsilon then return "\\upsilon "
        elif ff=phi then return "\\phi "
        elif ff=chi then return "\\chi "
        elif ff=psi then return "\\psi "
        elif ff=omega then return "\\omega "
        elif ff=Alpha then return "\\Alpha "
        elif ff=Beta then return "\\Beta ";
        elif ff=Gamma then return "\\Gamma "
        elif ff=Delta then return "\\Delta "
        elif ff=Epsilon then return "\\Epsilon "
        elif ff=Zeta then return "\\Zeta "
        elif ff=Eta then return "\\Eta"
        elif ff=Theta then return "\\Theta "
        elif ff=Iota then return "\\Iota "
        elif ff=Kappa then return "\\Kappa "
        elif ff=Lambda then return "\\Lambda "
        elif ff=Mu then return "\\Mu "
        elif ff=Nu then return "\\Nu "
        elif ff=Xi then return "\\Xi "
        elif ff=Omicron then return "\\Omicron "
        elif ff=PI then return "\\Pi "
        elif ff=Rho then return "\\Rho "
        elif ff=Sigma then return "\\Sigma "
        elif ff=Tau then return "\\Tau "
        elif ff=Upsilon then return "\\Upsilon "
        elif ff=Phi then return "\\Phi "
        elif ff=Chi then return "\\Chi "
        elif ff=Psi then return "\\Psi "
        elif ff=Omega then return "\\Omega "
        else
          return convert(ff,string):
        end if:
      end proc:


    end module: # Maple2TeX

    getTeX:=proc(expr,{clip::boolean:=false,cdots::boolean:=false,verbose:=false})
      local st, ci:
      if verbose then Maple2TeX:-verbose:=true: else Maple2TeX:-verbose:=false: end if:
      st:=convert(Maple2TeX:-getstr(expr),string):
      if cdots then
        if clip then Export("/tmp/mapleclip.txt",st); system(`xclip -sel clip < "/tmp/mapleclip.txt"`): end if:
        return convert(st,name):
      else
        ci:=StringTools:-Search("\\cdot ",st):
        while ci>0 do
          st:=cat(st[1..ci-2],st[ci+5..length(st)]):
          ci:=StringTools:-Search("\\cdot ",st):
        end do:
        if clip then Export("temp.txt",st); system(`xclip -sel clip < "temp.txt"`): end if:
        return convert(st,name):
      end if:
    end proc:


    ####################################################################################
    ####################################################################################
    ##                             (x+y)^n to power series                            ##
    ####################################################################################
    ####################################################################################

    binomexpand := proc( ee,{index::name:=k,mainvar::integer:=2,breakoff::boolean:=false} )
      local A,B,V,L,E,K;
      if (op(0,ee)=`sin`) then E:=(1-cos(op(1,op(1,ee)))^2)^(1/2); elif (op(0,ee)=`cos`) then E:=(1-sin(op(1,ee))^2)^(1/2); elif (op(0,op(1,ee))=`sin` and op(0,ee)=`^`) then E:=(1-cos(op(1,op(1,ee)))^2)^(op(2,ee)/2); elif (op(0,op(1,ee))=`cos` and op(0,ee)=`^`) then E:=(1-sin(op(1,op(1,ee)))^2)^(op(2,ee)/2); else E:=ee;
      end if;
      if (op(0,op(1,E))=`+` and op(0,E)=`^`) then
        A:=op(mainvar,op(1,E));
        B:=op(1,E)-A;
        V:=op(2,E);
        if (is(V,nonnegint) or breakoff) then L:=V; else L:=infinity; end if;
        return subs(K=index,Sum(binomial(V,K)*A^K*B^(V-K),K=0..L));
      else
        error `Argument is not of the form (a+b)^c.`;
      end if;
    end proc:


    ####################################################################################
    ####################################################################################
    ##                             Coordinate change tools                            ##
    ####################################################################################
    ####################################################################################

    coordtools:=module()
     export asumts,getcsys,Coos,Coordsyss:
     local findcoord:

      asumts:=r1>=0,r2>=0,r12>=0,r12<=r1+r2,r12>=abs(r1-r2),rz<=r1+r2,rz>=abs(r1-r2),d>0,d<sqrt(2),z>0,z<sqrt(2), r>=0,alpha>=0,alpha<=Pi,beta>=0,beta<=Pi,a>=-1,a<=1,b>=0,b<=1,theta>=0,theta<=Pi,v>=-1,v<=1,w>=-1,w<=1:
      
      Coos:=LinearAlgebra:-Transpose(Matrix([
        [`Coordinate definitions`, r = sqrt(r1^2+r2^2), alpha = arccos((r1^2-r2^2)/(r1^2+r2^2)), d = r12/sqrt(r1^2+r2^2), a = (r1^2-r2^2)/(r1^2+r2^2),b=2*r1*r2/(r1^2+r2^2), theta = arccos((1/2)*(r1^2-r12^2+r2^2)/(r1*r2)), v = (1/2)*(r1^2-r12^2+r2^2)/(r1*r2), w = (r1^2-r12^2+r2^2)/(r1^2+r2^2),  rho = r1/r2, r1 = r1, r2 = r2, r12 = r12, s = r1+r2, t = r1-r2, u = r12, p = r12/(r1+r2), q = (r1-r2)/r12, U=(r2+r12-r1), V=(r1+r12-r2), W=2*(r1+r2-r12), tau = (r1-r2)/(r1+r2), sigma = r1/r12, Tau = r2/r12, zeta=(arccos((r1^2-r2^2)/(r1^2+r2^2)))/2+Pi/4, beta = arccos((r1^2-r12^2+r2^2)/(r1^2+r2^2)),
        rz = sqrt(2*r1^2+2*r2^2-r12^2),z = sqrt(2-r12^2/(r1^2+r2^2))],
        [`Relations etc.`,`Hyperradius`,`Hyperangle`,d = r12/r,a=cos(alpha),b=sin(alpha),``,v=cos(theta),w=sin(alpha)*cos(theta),``,`Interparticle`,``,``,`Hyleraas`,``,``,`Kinoshita`,``,`Pekeris`,``,``,``,``,``,``,``,``,``]]));

      
      Coordsyss:=Matrix([["Name","Coordinates","r1r2r12 -> Coordinate system","Coordinate system -> r1r2r12"],
      [ralphad, [r, alpha, d], [r = sqrt(r1^2+r2^2), alpha = arccos((r1^2-r2^2)/(r1^2+r2^2)), d = r12/sqrt(r1^2+r2^2)],
       [r1 = (sqrt(1/2))*r*sqrt(1+cos(alpha)), r2 = sqrt(1/2)*r*sqrt(1-cos(alpha)), r12 = r*d]]
      ,[rad, [r, a, d], [r = sqrt(r1^2+r2^2), a = (r1^2-r2^2)/(r1^2+r2^2), d = r12/sqrt(r1^2+r2^2)],
       [r1 = sqrt(1/2)*r*sqrt(1+a), r2 = sqrt(1/2)*r*sqrt(1-a), r12 = r*d]]
      ,[ralphatheta, [r, alpha, theta], [r = sqrt(r1^2+r2^2), alpha = arccos((r1^2-r2^2)/(r1^2+r2^2)),
       theta = arccos((1/2)*(r1^2-r12^2+r2^2)/(r1*r2))], [r1 = sqrt(1/2)*r*sqrt(1+cos(alpha)), r2 = sqrt(1/2)*r*sqrt(1-cos(alpha)),
       r12 = r*sqrt(1-cos(theta)*sin(alpha))]]
      ,[ralphav, [r, alpha, v], [r = sqrt(r1^2+r2^2), alpha = arccos((r1^2-r2^2)/(r1^2+r2^2)), v = (1/2)*(r1^2-r12^2+r2^2)/(r1*r2)],
       [r1 = sqrt(1/2)*r*sqrt(1+cos(alpha)), r2 = sqrt(1/2)*r*sqrt(1-cos(alpha)), r12 = r*sqrt(1-v*sin(alpha))]]
      ,[rav, [r, a, v], [r = sqrt(r1^2+r2^2), a = (r1^2-r2^2)/(r1^2+r2^2), v = (1/2)*(r1^2-r12^2+r2^2)/(r1*r2)],
       [r1 = sqrt(1/2)*r*sqrt(1+a), r2 = sqrt(1/2)*r*sqrt(1-a), r12 = r*sqrt(1-v*sqrt(1-a^2))]]
      ,[rbv, [r, b, v], [r = sqrt(r1^2+r2^2), b = 2*r1*r2/(r1^2+r2^2), v = (1/2)*(r1^2-r12^2+r2^2)/(r1*r2)],
       [r1 = r*b/(sqrt(1+b)+sqrt(1-b)), r2 = r/2*(sqrt(1+b)+sqrt(1-b)), r12 = r*sqrt(1-v*b)]]
      ,[raw, [r, a, w], [r = sqrt(r1^2+r2^2), a = (r1^2-r2^2)/(r1^2+r2^2), w = (r1^2-r12^2+r2^2)/(r1^2+r2^2)],
       [r1 = sqrt(1/2)*r*sqrt(a+1), r2 = sqrt(1/2)*r*sqrt(1-a), r12 = r*sqrt(1-w)]]
      ,[ralphaw, [r, alpha, w], [r = sqrt(r1^2+r2^2), alpha = arccos((r1^2-r2^2)/(r1^2+r2^2)), w = (r1^2-r12^2+r2^2)/(r1^2+r2^2)],
       [r1 = sqrt(1/2)*r*sqrt(1+cos(alpha)), r2 = sqrt(1/2)*r*sqrt(1-cos(alpha)), r12 = sqrt(-w+1)*r]]
      ,[rrhov, [r, rho, v], [r = sqrt(r1^2+r2^2), rho = r1/r2, v = (1/2)*(r1^2-r12^2+r2^2)/(r1*r2)],
       [r1 = r*rho*sqrt(1/(rho^2+1)), r2 = r*sqrt(1/(rho^2+1)), r12 = r*sqrt((-2*v*rho+rho^2+1)/(rho^2+1))]]
      ,[rrhod, [r, rho, d], [r = sqrt(r1^2+r2^2), rho = r1/r2, d = r12/sqrt(r1^2+r2^2)],
       [r1 = r*rho*sqrt(1/(rho^2+1)), r2 = r*sqrt(1/(rho^2+1)), r12 = r*d]]
      ,[stu, [s, t, u], [s = r1+r2, t = r1-r2, u = r12], [r1 = (s+t)/2, r2 = (s-t)/2, r12 = u]]
      ,[uvw, [U,V,W], [U=(r2+r12-r1), V=(r1+r12-r2), W=2*(r1+r2-r12)], [r1 = W/4+V/2, r2 = W/4+U/2, r12 = V/2+U/2]]
      ,[stauq, [s, tau, q], [s = r1+r2, tau = (r1-r2)/(r1+r2), q = r12/(r1+r2)], [r1 = s*(1+tau)/2, r2 = s*(1-tau)/2, r12 = q*s]]
      ,[spq, [s, p, q], [s = r1+r2, p = (r1-r2)/r12, q = r12/(r1+r2)], [r1 = s*(1+p*q)/2, r2 = s*(1-p*q)/2, r12 = q*s]]
      ,[sigTauu, [sigma, Tau, u], [sigma = r1/r12, Tau = r2/r12, u = r12], [r1 = sigma*u, r2 = Tau*u, r12 = u]]
      ,[ri, [r1,r2,r12], [r1 = r1, r2 = r2, r12 = r12], [r1 = r1, r2 = r2, r12 = r12]]
      ,[ralphabeta, [r, alpha, beta], [r = sqrt(r1^2+r2^2), alpha = arccos((r1^2-r2^2)/(r1^2+r2^2)), beta = arccos((r1^2-r12^2+r2^2)/(r1^2+r2^2))],
       [r1 = sqrt(1/2)*r*sqrt(1+cos(alpha)), r2 = sqrt(1/2)*r*sqrt(1-cos(alpha)), r12 = r*sqrt(1-cos(beta))]]
      ,[riz, [r1, r2, rz], [r1 = r1, r2 = r2, rz = sqrt(2*r1^2-r12^2+2*r2^2)], [r1 = r1, r2 = r2, r12 = sqrt(2*r1^2+2*r2^2-rz^2)]]
      ,[raz, [r, a, z], [r = sqrt(r1^2+r2^2), a = (r1^2-r2^2)/(r1^2+r2^2), z = sqrt(2-r12^2/(r1^2+r2^2))], [r1 = (1/2)*sqrt(2)*r*sqrt(a+1), r2 = (1/2)*sqrt(2)*r*sqrt(1-a), r12 = r*sqrt(-z^2+2)]]
      ,[radz, [r, a, d, z], [r = sqrt(r1^2+r2^2), a = (r1^2-r2^2)/(r1^2+r2^2), d=r12/(r1^2+r2^2), z = sqrt(2-r12^2/(r1^2+r2^2))], [r1 = (1/2)*sqrt(2)*r*sqrt(a+1), r2 = (1/2)*sqrt(2)*r*sqrt(1-a), r12 = r*d]]
      ,[ridz, [r, a, d, z], [r1 = r1, r2 = r2, r12 = r12, rz = sqrt(2*r1^2-r12^2+2*r2^2)], [r1 = r1, r2 = r2, r12 = r12]]
      ]):
      

     findcoord:=proc(cc)
        description "Recognizes a term as a coordinate in the list Coos. Returns index of coordinate or 0 if nothing was found.":
        local rhslist,oi,ii:
        rhslist:=[0,seq(rhs(Coos(ii)),ii=2..LinearAlgebra:-RowDimension(Coos))]:
        oi:=0:
        for ii from 1 to nops(rhslist) do
          if (simplify(cc-rhslist[ii]) assuming asumts)=0 then
            oi:=ii:
          end if:
        end do:
        return oi:
      end proc:
      
      getcsys:=proc(cc)
        description "From multiple possible forms of coordinate system specifications (name, set of known coordinates, set of coordinate definitions (possibly assigned a name)), the coordinate transformations new coordinate system -> r1r2r12 and r1r2r12 -> new coordinate system are returned.":
        local ci:=0, jj, oi, tempcv, tempeq, tempeqs, useraliases:=[]:

        # If input is a name of the form raw, return corresponding coordinate transformations.
        if type(cc,name) and ListTools:-Search(cc,[seq(Coordsyss(ii,1),ii=2..LinearAlgebra:-RowDimension(Coordsyss))])>0 then
          ci:=ListTools:-Search(cc,[seq(Coordsyss(ii,1),ii=1..LinearAlgebra:-RowDimension(Coordsyss))]):
          return [op(eval([Coordsyss(ci,3), Coordsyss(ci,4)],useraliases))]:
      
        # If input is a list of some form, bring it into coordinate transform shape, then see if it is known already.
        elif type(cc,set) or type(cc,list) and nops(cc)=3 then
      
          # Type {r1=f(coords),...}  (Works only for known systems, since otherwise the new coordinate names are unknown.)
          if type([op(cc)],list(name=algebraic)) and {seq(lhs(op(ii,cc)),ii=1..3)}={r1,r2,r12} then
            ci:=ListTools:-Search({op(cc)},[0,seq({op(Coordsyss(ii,4))},ii=2..LinearAlgebra:-RowDimension(Coordsyss))]):
            if ci>0 then
              return [Coordsyss(ci,3), Coordsyss(ci,4)]:
            else
              ERROR("Sorry, no coordinate system recognized. Try specifying your system in the form {new_coord1=f(r1,r2,r12),...}."):
            end if:
          end if:
      
          for jj from 1 to 3 do
      
            # Case coordinate=f(r1,r2,r12)
            tempcv:=op(jj,cc):
            oi:=ListTools:-Search(tempcv,[0,seq(lhs(Coos(ii,1)),ii=2..LinearAlgebra:-RowDimension(Coos))]):  # Look up coordinate names
            if oi>0 then 
              tempeq[jj]:=Coos(oi,1):
            elif type(tempcv,algebraic) then  # Look up coordinate definitions
              tempcv:=eval(tempcv,[seq(Coos(ii,1),ii=2..LinearAlgebra:-RowDimension(Coos))]): #Allow usage of all known coordinates
              oi:=findcoord(tempcv):
              if oi>0 then tempeq[jj]:=Coos(oi): else tempeq[jj]:=C||jj=tempcv: end if:
            elif type(tempcv,name=algebraic) then  # Look up coordinate definitions
              tempcv:=lhs(tempcv)=eval(rhs(tempcv),[seq(Coos(ii,1),ii=2..LinearAlgebra:-RowDimension(Coos))]): #Allow usage of all known coordinates
              oi:=findcoord(rhs(tempcv)):
              if oi>0 then tempeq[jj]:=Coos(oi):
                if not lhs(Coos(oi))=lhs(tempcv) then useraliases:=[op(useraliases),lhs(Coos(oi))=lhs(tempcv)]: end if:  #remember deviating names
              else tempeq[jj]:=tempcv: end if:
            end if:
          end do:
      
          # Coordinate transform set, will be looked up in coordinate system collection, otherwise calculate {r1=...,r2=...,r12=...} set.
          tempeqs:={seq(tempeq[jj],jj=1..3)}:
          ci:=ListTools:-Search(tempeqs,[0,seq({op(Coordsyss(ii,3))},ii=2..LinearAlgebra:-RowDimension(Coordsyss))]):
        
          if ci>0 then
            return [op(eval([Coordsyss(ci,3), Coordsyss(ci,4)],useraliases))]:   # Look it up
          else
            convert(solve(tempeqs,[r1,r2,r12]),radical):                         # Solve for  {r1=...,r2=...,r12=...} set if possible.
            if nops(%)>0 then
              return [[op(tempeqs)], (simplify(op(%)) assuming asumts)]:
            else print(tempeqs):
              ERROR("Coordinate system could not be solved for [r1,r2,r12]"):
            end if:
          end if:
        end if:

        ERROR("No coordinate system recognized"):
      end proc:

    end module:
    
    `&>`:=proc(l1,l2:="NE")
      if l2="NE" then  # Workaround to make first parameter optional (:=ri)
        return op(2,coordtools:-getcsys(l1)):
      end if:
      if l2=ri then
        return op(1,coordtools:-getcsys(l1)):  # This case is not really necessary, just to avoid simplification messing with the result.
      elif l1=raz and l2=riz then
        return [r = sqrt(r1^2+r2^2), a = (r1^2-r2^2)/(r1^2+r2^2), z = rz/sqrt(r1^2+r2^2)];
      else
        map(zz->lhs(zz)=simplify(eval(rhs(zz),op(2,coordtools:-getcsys(l2)))),op(1,coordtools:-getcsys(l1)));
        simplify(expand(combine(%, symbolic))) assuming coordtools:-asumts;
        return %;
      end if:
    end proc:

    showcoord:=proc(cc:=`showall`)
      local oi,ci,oldrtsize:
      oldrtsize:=interface(rtablesize=infinity):
      oi:=ListTools:-Search(cc,[0,seq(lhs(coordtools:-Coos(ii,1)),ii=2..LinearAlgebra:-RowDimension(coordtools:-Coos))]):
      ci:=ListTools:-Search(cc,[seq(coordtools:-Coordsyss(ii,1),ii=1..LinearAlgebra:-RowDimension(coordtools:-Coordsyss))]):
      if cc=`showall` then
        print(coordtools:-Coos);
        print(coordtools:-Coordsyss);
      elif cc=`coords` or cc=`coordinates` then
        print(coordtools:-Coos);
      elif cc=`csys` or cc=`coordinate systems` or cc=`systems` then
        print(coordtools:-Coordsyss);
      elif oi>0 then
        print(coordtools:-Coos(oi,1), coordtools:-Coos(oi,2)):
      elif ci>0 then
        print(seq(coordtools:-Coordsyss(ci,ii),ii=3..4)):
      end if:
      interface(rtablesize=oldrtsize):
      return ``:
    end proc:

    assumecoords:=proc(state:=on)
      global r,a,d,z,r1,r2,r12,rz,alpha,theta,v,w,s,t,u;
      if state=on then
        assume(r>=0);
        assume(-1<=a,a<=1);
        assume(0<=d,d<=sqrt(2));
        assume(0<=z,z<=sqrt(2));
        assume(r1>=0,r2>=0,r12>=0,rz>=0,r1+r2>=r12,r1+r12>=r2,r12+r2>=r1,r1-r2<=r12,r1-r12<=r2,r12-r2<=r1,r2-r1<=r12,r12-r1<=r2,r2-r12<=r1,r1+r2>=rz,r1+rz>=r2,rz+r2>=r1,r1-r2<=rz,r1-rz<=r2,rz-r2<=r1,r2-r1<=rz,rz-r1<=r2,r2-rz<=r1);
        assume(0<=alpha,alpha<=Pi);
        assume(0<=theta,theta<=Pi);
        assume(-1<=v,v<=1);
        assume(-1<=w,w<=1);
        assume(0<=s,0<=u,t<=u,-t<=u,u<=s,t<=s);
        return `on`;
      else
        r:='r';
        a:='a';
        d:='d';
        z:='z';
        r1:='r1';
        r2:='r2';
        r12:='r12';
        rz:='rz';
        alpha:='alpha';
        theta:='theta';
        v:='v';
        w:='w';
        s:='s';
        t:='t';
        u:='u';
        return `off`;
      end if:
    end proc:

    assumeinds:=proc(state)
      global i,j,k,l,n,m;
      local ind:
      if state=on or is(state,list) then
        for ind in [i,j,k,l,n,m] do
          if is(ind,name) then
            assume(ind::nonnegint);
          end if:
        end do:
        return `on`;
      else
        if is(i,name) then i:='i': end if:
        if is(j,name) then j:='j': end if:
        if is(k,name) then k:='k': end if:
        if is(l,name) then l:='l': end if:
        if is(n,name) then n:='n': end if:
        if is(m,name) then m:='m': end if:
        return `off`;
      end if:
    end proc:



    ####################################################################################
    ####################################################################################
    ##                       Laplacian in different coordinates                       ##
    ####################################################################################
    ####################################################################################

    L:=proc(cc:=ri)
     local Lapl,treq:
     
     # Special cases, needing extra simplification etc
     if cc=`ralphabeta` or {op(cc)}={r,alpha,beta} then
       unapply(subs(f(alpha, beta, r)=f,
       -2*(diff(f(alpha, beta, r), alpha, alpha))/r^2-2*(diff(f(alpha, beta, r), beta, beta))/r^2
       -4*cos(alpha)*(diff(f(alpha, beta, r), alpha))/(r^2*sin(alpha))-4*cos(beta)*(diff(f(alpha, beta, r), beta))/(r^2*sin(beta))
       +4*cos(beta)*cos(alpha)*(diff(f(alpha, beta, r), beta, alpha))/(r^2*sin(alpha)*sin(beta))
       -(5/2)*(diff(f(alpha, beta, r), r))/r-(1/2)*(diff(f(alpha, beta, r), r, r))),f);
       return %:
     end if:
     
     if cc=`ridz` or {op(cc)}={r1,r2,r12,rz} then # Chosen such that powers of r12 and rz never rise
       unapply(subs(f(rz, r12, r1, r2)=f,-(1/2)*(diff(f(rz, r12, r1, r2), r1, r1))-(1/2)*(diff(f(rz, r12, r1, r2), r2, r2))-(diff(f(rz, r12, r1, r2), r12, r12))-(diff(f(rz, r12, r1, r2), rz, rz))-(1/2)*(r1^2+r12^2-r2^2)*(diff(f(rz, r12, r1, r2), r12, r1))/(r12*r1)-(1/2)*(r1^2-r2^2+rz^2)*(diff(f(rz, r12, r1, r2), rz, r1))/(rz*r1)-(1/2)*(-r1^2+r12^2+r2^2)*(diff(f(rz, r12, r1, r2), r2, r12))/(r12*r2)-(1/2)*(-r1^2+r2^2+rz^2)*(diff(f(rz, r12, r1, r2), rz, r2))/(r2*rz)-(diff(f(rz, r12, r1, r2), r1))/r1-(diff(f(rz, r12, r1, r2), r2))/r2-2*(diff(f(rz, r12, r1, r2), r12))/r12-2*(diff(f(rz, r12, r1, r2), rz))/rz),f);
       return %:
     end if:
     
     if cc=`radz` or {op(cc)}={r,a,d,z} then
       (2*(a^2-1))*(diff(f(r, z, d, a), a, a))/r^2+6*a*(diff(f(r, z, d, a), a))/r^2+(1/2)*(d^2-2)*(diff(f(r, z, d, a), d, d))/r^2+(1/2)*(z^2-2)*(diff(f(r, z, d, a), z, z))/r^2+2*a*(d^2-1)*(diff(f(r, z, d, a), d, a))/(r^2*d)+2*a*(z^2-1)*(diff(f(r, z, d, a), z, a))/(r^2*z)+d*z*(diff(f(r, z, d, a), z, d))/r^2+(1/2)*(5*d^2-4)*(diff(f(r, z, d, a), d))/(r^2*d)+(1/2)*(5*z^2-4)*(diff(f(r, z, d, a), z))/(r^2*z)-(5/2)*(diff(f(r, z, d, a), r))/r-(1/2)*(diff(f(r, z, d, a), r, r));
       return %:
     end if:
     
     # General case

     Lapl:=proc(f)
       -1/2*diff(f,r1,r1)-1/r1*diff(f,r1)-1/2*diff(f,r2,r2)-1/r2*diff(f,r2)-diff(f,r12,r12)-2/r12*diff(f,r12)
           -(r1^2-r2^2+r12^2)/2/r1/r12*diff(f,r1,r12)-(r2^2-r1^2+r12^2)/2/r2/r12*diff(f,r2,r12): end proc:

      treq:=map(zz->lhs(zz)=eval(rhs(zz),{r1=RR1,r2=RR2,r12=RR12}),{op(op(2,coordtools:-getcsys(cc)))}):
      eval(collect(PDEtools:-dchange(treq,[Lapl(f(r1,r2,r12)),f(r1,r2,r12)]),diff,
        zz->factor(simplify(collect(numer(zz),v,factor)/collect(denom(zz),v,factor)))),{RR1=r1,RR2=r2,RR12=r12}):
      collect(%,diff,zz->factor(numer(zz)/factor(expand(denom(zz))))):
      unapply(subs(op(2,%)=f,op(1,%)),f):
    end proc:

    ####################################################################################
    ####################################################################################
    ##                Hyperspherical Harmonics in different coordinates               ##
    ####################################################################################
    ####################################################################################

    HH:=proc(cc:=ri)
      local HyperHarmonic:

      if cc=ri then
        HyperHarmonic:=(r1^2+r2^2)^(1/2*n-l)*2^l*r1^l*r2^l*GegenbauerC(1/2*n-l,l+1,(r1^2-r2^2)/(r1^2+r2^2))*LegendreP(l,1/2*(r1^2-r12^2+r2^2)/r1/r2):
      else
        r^n*sqrt(1-a^2)^l*GegenbauerC(1/2*n-l,l+1,a)*LegendreP(l,(1-d^2)/sqrt(1-a^2)):
        HyperHarmonic:=simplify(eval(%,rad&>cc));
      end if:

      return proc(nn,ll) eval(HyperHarmonic,[n=nn,l=ll]): simplify(convert(%,elementary)); return %; end proc:
    end proc:
    
    ####################################################################################
    ####################################################################################
    ##                                dchange interface                               ##
    ####################################################################################
    ####################################################################################

    Dchange:=proc(eqns,expr,func:='z->z',{newvars:=NA,itr:={},known:={},unknown:={},params:={}})
      local dchset,tmpeqns,nv,A,B,P,S:
      if op(0,eqns)=`=` then
        dchset :=map(zz->zz=zz||temp,indets(rhs(eqns),name) minus indets(rhs(eqns),constant)):
        tmpeqns:=lhs(eqns)=eval(rhs(eqns),dchset):
      elif type(eqns,set) then
        dchset :=map(yy->op(map(zz->zz=zz||temp,indets(rhs(yy),name) minus indets(rhs(yy),constant))),eqns):
        tmpeqns:=map(yy->lhs(yy)=eval(rhs(yy),dchset),eqns):
      elif type(eqns,list) then
        dchset :={op(map(yy->op(map(zz->zz=zz||temp,indets(rhs(yy),name) minus indets(rhs(yy),constant))),eqns))}:
        tmpeqns:={op(map(yy->lhs(yy)=eval(rhs(yy),dchset),eqns))}:
      else
        error `expected a transformation equation or a set or list of them, received: `, eqns:
      end if;

      if newvars=`NA` then nv:=``: else nv := eval(newvars,dchset): end if:    
      PDEtools:-dchange(tmpeqns,expr,nv,itr, convert("known",name)=known,convert("unknown",name)=unknown,convert("params",name)=params,zz->collect(zz,[diff,int],func)):
      subs(map(zz->(rhs=lhs)(zz),dchset),%):
      if a in map(lhs,dchset) then
        eval(eval(algsubs(A+B=S,algsubs(A*B=P,eval(%,[sqrt(1+a)=A,sqrt(1-a)=B]))),[P=sqrt(1-a^2),S=sqrt(2)*sqrt(1+sqrt(1-a^2))]),[A=sqrt(1+a),B=sqrt(1-a)]):
      end if:
      return %:
    end proc:

    ####################################################################################
    ####################################################################################
    ##                        collect interface (works for sqrt)                      ##
    ####################################################################################
    ####################################################################################

    posfactor:=proc(expr)
      factors(expr);
      map(zz->seq(op(1,zz),ii=1..op(2,zz)),%[2]);
      `*`(op(map(yy->`if`(tcoeff(yy)<1,-yy,yy),%)));
      return factor(expr/%)*%;
    end proc:



     Collect:=proc(a, x, iform:=recursive, ifunc:='z->z')
      local X,A:=a,s:=[],xx,mx,xfac,form,func;

      if not iform in {recursive,distributed} then
        func:=iform:
      else
        form:=iform:
        func:=ifunc:
      end if:

      if type(x,list) or type(x,set) then
        X:=[op(x)]:
      else
        X:=[x]:
      end if:
      X:=eval(X,rp=ratpower);

      if 'ratpower' in X then                                     # Advanced roots detection
        indets[flat](a,`^`(anything,fraction));                   # All the roots
        eval(map(zz->zz=map(yy->yy^op(2,zz),posfactor(dummy*op(1,zz))),%),dummy=1); # Split products+adjust signs
        A:=eval(a,%);
        map(zz->`if`(op(0,zz)=`*`,op(zz),zz),subs(I=1,eval(%%%,%%)));
        map(zz->ratpower(op(1,zz),op(2,zz)-floor(op(2,zz))),%);   # All the root arguments and "mod1" of their powers
        ListTools:-Search(`ratpower`,X);
        X:=[op(X[1..%-1]),op(%%),op(X[%+1..-1])];
      end if:

      for xx in X do
        if op(0,xx)='ratpower' and nops(xx)=1 then                # Second ratpower argument not given
          posfactor(dummy*op(1,xx)):
          xfac:=`if`(is(op(1,%),constant),op(1,%),1);             # Ensure base is kept: xfac scales vs. normalized factors
          indets[flat](A,`^`(divisible(op(1,xx)),fraction));      # All the fractional powers of multiples of this argument
          eval(map(zz->zz=map(yy->(xfac*yy)^op(2,zz)/xfac^op(2,zz),posfactor(dummy*op(1,zz))),%),dummy=1); # Adjust factors
          A:=subs(%,A);
          indets[flat](A,`^`(id(op(1,xx)),fraction));             # All the fractional powers of this argument
          map(zz->ratpower(op(1,zz),op(2,zz)-floor(op(2,zz))),%); # All the ratpow arguments and "mod1" of their powers
          X:=eval(X,xx=op(%));
        elif op(0,xx)='ratpower' and nops(xx)=2 then              # Second ratpower argument given
          posfactor(dummy*op(1,xx)):
          xfac:=`if`(is(op(1,%),constant),op(1,%),1);             # Ensure base is kept: xfac scales vs. normalized factors
          indets[flat](A,`^`(divisible(op(1,xx)),mod1(op(2,xx))));  # All related powers of multiples of this argument
          eval(map(zz->zz=map(yy->(xfac*yy)^op(2,zz)/xfac^op(2,zz),posfactor(dummy*op(1,zz))),%),dummy=1); # Adjust factors
          A:=subs(%,A);
        end if:
      end do:
      X:=eval(X,ratpower=((x,y)->ratpower(x,y-floor(y))));
      X:=ListTools:-MakeUnique(X);
      X:=eval(X,ratpower=((x,y)->`if`(is(x,constant) or is(y,integer),NULL,ratpower(x,y))));

      for xx in X do
        if op(0,xx)='ratpower' then
          indets[flat](A,`^`(id(op(1,xx)),mod1(op(2,xx))));       # Find all related terms (same arg, power diff of 1)
          mx:=op(1,xx)^min(map(zz->op(2,zz),%));                  # Lowest of the related powers
          map(zz->zz=factor(zz/mx)*freeze(mx),%%);                # Freeze just mx
          A:=subs(%,A);                                           # Replace
          X:=eval(X,xx=freeze(mx));
        end if;
      end do:
      if sqrt in X then                                           # Sqrt detection
        indets[flat](a,`^`(`+`,halfint));
        [op(%),op(indets[flat](a,`^`(`*`,halfint)) minus %)];
        s:=[op(%),op(indets[flat](a,`^`(anything,halfint)) minus {op(%)})];   # Give sqrt of sums and products priority
        for xx from 1 to nops(s) do                               # Update A and X with frozen sqrt's.
          A:=subs(op(xx,s)=freeze(op(xx,s)),A);
        end do:
        X:=eval(X,'sqrt'=op(map(zz->freeze(zz),s))):
      end if:

      s:=[]:
      for xx in X do
        try collect(A,xx,form,func):
        catch : s:=[op(s),xx]:
        end try:
      end do:
      X:=eval(X,map(zz->zz=freeze(zz),s)):
      A:=eval(A,map(zz->zz=freeze(zz),s)):

      collect(A,X,form,func):
      return thaw(%);
    end proc:


    ####################################################################################
    ####################################################################################
    ##                      Invert simple polynomials in r1 r2 r12                    ##
    ####################################################################################
    ####################################################################################

    invertpolytools:=module()
      export invertrimonomial,tailzero,getTailMinus,getTailPlus:
      local getans,getlnans,getlnnonsingans,getTminusSym:

      ########################################################
      #  Inverts monomials of the form r1^i*r2^j*r12^k*rz^l. #
      ########################################################
      #   Returns: [inverted terms, terms left to invert].   #
      ########################################################
      

      getans:=proc(h,rpl,sym:=0)
        local ans:=0,i,j,k,l,cc:=0,vars,negexps;
        for l from -rpl[4] to rpl[4] by 2 do
          for k from -rpl[3] to h-l+2 by 2 do
            for j from -rpl[2] to h-l-k+1 by 2 do
              i:=h-l-k-j:
              if i>-2 then
                negexps:=`+`(op(map(zz->min(zz,0),[i,j,k,l])));
                c[cc]*b[negexps]*(r1^i*r2^j+sym*r1^j*r2^i)*r12^k*rz^l:
                ans:=ans+%:
                cc:=cc+1:
              end if:
            end do:
          end do:
        end do:
        vars:=map(zz->`if`(op(0,zz)=`c`,zz,NULL),indets(ans,name));
        return eval(ans,b[0]=1),vars;
      end proc:

      getlnans:=proc(h,rpl,sym:=0)
        local lns:=0, lna:=0, nn, ans, vars, lnans:
        for nn from 0 to h/2 do
          if is(h/2-nn,even) then
            lns:=lns+x[nn]*simplify(HH()(h,nn));
          else
            lna:=lna+x[nn]*simplify(HH()(h,nn));
          end if:
        end do:
        ans,vars:=getans(h,rpl,sym):
        lnans:=(`if`(sym>-1,lns,0)+`if`(sym<1,lna,0))*(-2)*arctanh(r12/(r1+r2))
              +eval((`if`(sym>-1,lna,0)+`if`(sym<1,lns,0))*(-2)*arctanh((r1-r2)/r12),[seq(x[nn]=y[nn],nn=0..h/2)])
              +ans;
        vars:=vars union map(zz->`if`(op(0,zz)=`x` or op(0,zz)=`y`,zz,NULL),indets(lnans,name));
        return lnans,vars;
      end proc:

      getlnnonsingans:=proc(h,rpl,sym:=0)
        local lns:=0, lna:=0, Tplussym:=0, Tplusanti:=0, Tminussym:=0, Tminusanti:=0, nn, ans, vars, lnans:
        for nn from 0 to h/2 do
          if is(h/2-nn,even) then
            lns:=lns+x[nn]*simplify(HH()(h,nn));
            Tplussym:=Tplussym+x[nn]*TailPlus(h,nn);
            Tminusanti:=Tminusanti+x[nn]*TailMinus(h,nn);
          else
            lna:=lna+x[nn]*simplify(HH()(h,nn));
            Tplusanti:=Tplusanti+x[nn]*TailPlus(h,nn);
            Tminussym:=Tminussym+x[nn]*TailMinus(h,nn);
          end if:
        end do:
        ans,vars:=getans(h,rpl,sym):
        lnans:=(`if`(sym>-1,lns,0)+`if`(sym<1,lna,0))*Block1+`if`(sym>-1,Tplussym,0)+`if`(sym<1,Tplusanti,0)
              +eval((`if`(sym>-1,lna,0)+`if`(sym<1,lns,0))*Block2+`if`(sym>-1,Tminussym,0)+`if`(sym<1,Tminusanti,0),[seq(x[nn]=y[nn],nn=0..h/2)])
              +ans;
        vars:=vars union map(zz->`if`(op(0,zz)=`x` or op(0,zz)=`y`,zz,NULL),indets(lnans,name));
        return lnans,vars;
      end proc:
      
      getTminusSym:=proc(hh,ll)
        local sol:=0, TBI, TBIa, TBId, ans, tail, pl, ii, soly:
        HH(rad)(hh,ll);
        -(16*arccos((1/2)*sqrt(2)*d)/(Pi*d*sqrt(-d^2+2)*r^2))*(diff(Y(a, r, d), a))
        +(4*arcsin(a)/(Pi*d*sqrt(-a^2+1)*r^2))*(diff(Y(a, r, d), d));
        TBI:=collect(eval(%,Y(a, r, d)=%%),[arccos,arcsin],simplify);
        TBId:=coeff(TBI,arccos((1/2)*sqrt(2)*d))*sqrt(2-d^2);
        TBIa:=coeff(TBI,arcsin(a))*sqrt(-a^2+1);

        if not TBIa=0 then
          ans:=r^(degree(TBIa,r)+2)*add(add(x[k,i]*a^i,i=0..hh)*d^(2*k),k=0..degree(TBIa,d)/2);
          coeff(collect(L(rad)(ans*arcsin(a)*sqrt(1-a^2)),[arcsin,r],simplify),arcsin(a))*sqrt(-a^2+1)/r^degree(TBIa,r);
          [coeffs(collect(%-TBIa/r^degree(TBIa,r),[d,a],distributed,simplify),{d,a})];
          sol:=sol+factor(eval(ans,solve(%)))*arcsin(a)*sqrt(1-a^2);
        end if:

        if not TBId=0 then
          ans:=r^(degree(TBId,r)+2)*add(add(x[n,i]*d^i,i=0..hh)*a^(2*n),n=0..degree(TBId,a)/2);
          coeff(collect(L(rad)(ans*arccos((1/2)*sqrt(2)*d)*sqrt(2-d^2)),[arcsin,r],simplify),arccos((1/2)*sqrt(2)*d))*sqrt(2-d^2)/r^(hh-2);
          expand(simplify(%));
          [coeffs(collect(%-TBId/r^degree(TBId,r),[d,a],distributed,simplify),{d,a})];
          sol:=sol+factor(eval(ans,solve(%)))*arccos((1/2)*sqrt(2)*d)*sqrt(2-d^2);
        end if:

        simplify(TBI-L(rad)(sol));
        ans:=add(x[m]*HH(rad)(hh,m),m=0..hh/2)*ln(r)
        +add(add(r^hh*y[n,k]*d^(2*k),k=0..hh)*a^(2*n),n=0..hh);
        collect(simplify(L(rad)(ans))-%%,[ln,a,d],distributed);
        tail:=eval(ans,solve([coeffs(eval(%,r=1),{a,d})]));
        pl:=eval(sort(eval([op(collect(%-op(1,%),[d,a],distributed))],d=a),(x,y)->degree(x,a)>degree(y,a)),[r=1,a=1]);
        for ii from 1 to nops(pl) do
          soly:=solve(pl[ii],indets(pl[ii]));
          if nops([soly])>0 then pl:=eval(pl,soly); tail:=eval(tail,soly); end if: # evs:=evs union map(zz->`if`((lhs=rhs)(zz),NULL,zz),soly): print(evs):
        end do:
        sol:=collect(sol+tail,[arcsin,arccos,ln],simplify);

        simplify(L(rad)(sol)-TBI);
        if %=0 then return sol; else error(hh,ll,"Something went wrong! Diff = ",%); end if;
      end proc:

      getTailMinus:=proc(h,l)
        if is(h/2-l,odd) then return getTminusSym(h,l); else WARNING(cat(Tminus[h,l], " not implemented, set to zero!")); return 0; end if:
      end proc:

      getTailPlus:=proc(h,l)
        local pl,ii,soly,tail:
        -1/r1*diff(Y(r1,r2,r12),r1)-1/r2*diff(Y(r1,r2,r12),r2)+(r1-r2)^2/r1/r2/r12*diff(Y(r1,r2,r12),r12);
        eval(%,Y(r1,r2,r12)=HH()(h,l));
        if %=0 then 0 else invertpolynomial(%); end if;
        tail:=%+invertpolynomial(0,h)+eval(invertpolynomial(0,h),[r1=r2,r2=r1]);
        pl:=eval(sort([op(collect(%,[r1,r2,r12],distributed))],(x,y)->2*degree(x,r12)+degree(x,r1)>2*degree(y,r12)+degree(y,r1)),[r1=1,r2=1,r12=1]);
          for ii from 1 to nops(pl) do
            soly:=solve(pl[ii],indets(pl[ii]));
            if nops([soly])>0 then pl:=eval(pl,soly); tail:=eval(tail,soly); end if:
          end do:
        return simplify(tail);
      end proc:

      invertrimonomial:=proc(t,symmetry:=0,nonsingular:=false,hom:=-infinity)
        local ans, vars, rpl, sol, nn, h:=hom, ans2, vars2:

        if hom=-infinity then 
          if t=0 then ERROR(`Please specify homogeneity in the second argument: invertpolynomial(0,h);`);
          else h:=2+degree(eval(t,[r1 = r*p, r2 = r*q, r12 = r*d,rz=r*z]),r);
          end if:
        end if:

        if t=0 and h=0 then return [c/2+symmetry/2*c,0]; end if;
        if t=0 and is(h,even) then return map(zz->zz/2+symmetry*zz/2,[add(c[ll]*factor(HH(ri)(h,ll)),ll=0..h/2),0]); end if;

        rpl:=map(zz->`if`(is(degree(op(1,expand(t)+dummy),zz),odd),1,0),[r1,r2,r12,rz]); # ri exponent parity list
        if `+`(op(rpl))<2 or rpl=[1,1,0,0] then # pure poly ansatz
           ans,vars:=getans(h,rpl,symmetry):
        elif rpl in {[1,0,1,0],[0,1,1,0]} then  # psi2bc-type logarithmic case
           ans,vars:=getlnans(h,rpl,symmetry);
           if nonsingular then ans2,vars:=getlnnonsingans(h,rpl,symmetry); end if;
        else return [0,t];                      # Case with no known solution
        end if:

        [coeffs(collect(simplify(L()(ans)-t),[r1,r2,r12,rz],distributed),[r1,r2,r12,rz])]:
        [solve(%,vars)]:
        if nops(%)=0 then return [0,t]; else if nonsingular then sol:=eval(ans2,%[1]); else  sol:=eval(ans,%[1]); end if; end if;
        if t=0 then
          sol:=eval(sol,[b[-4]=1,b[-3]=1,b[-2]=1,b[-1]=1]);
          return [sol,0];
        end if:
        # Remove the terms from the solution that have the most negative exponents (carefully, b[n] can be in the denominator)
        for nn from -4 to -1 do
          try
            sol:=eval(sol,b[nn]=0);
          catch:
            sol:=eval(sol,b[nn]=1);
          end try:
        end do:
        sol:=eval(sol,map(zz->zz=0,vars)); # Then remove all other unnecessary terms.
        return [collect(sol,[ln,arctanh,Block1,Block2,Z,rz,r12],simplify),0];;
      end proc:

      tailzero:=proc(h,l)
        return 0
      end proc:



    end module: #invertpolytools
      
      
            #########################################
            #  Inverts polynomials in r1,r2,r12,rz. #
    ########################################################
    #   Returns: [inverted terms, terms left to invert].   #
    ########################################################
    
   
   invertpolynomial:=proc(poly,h := -infinity, {nonsingular:=false})
      local p:=expand(poly+dummy),pp,pa:=[],ts:=[0,0],dc:=[r1 = sqrt(1/2)*r*(1+a)^(1/2), r2 = sqrt(1/2)*r*(1-a)^(1/2), r12 = r*d,rz=r*sqrt(2-d^2)],symmetry:=0:
        if simplify(p-eval(p,[r1=r2,r2=r1]))=0 then symmetry:=+1; # Entire poly is symmetrical in a
        elif simplify(p+eval(p,[r1=r2,r2=r1]))=0 then symmetry:=-1; # Entire poly is antisymmetrical in a
        end if:
        if symmetry=0 then pa:=[op(p)]:
        else
          while op(0,p)=`+` do
            pp:=op(1,p):
            # if pp is already (anti)symmetrical: 
            if (simplify(pp-symmetry*eval(pp,[r1=r2,r2=r1]))=0) then
              pa:=[op(pa),pp]:
              p:=expand(simplify(p-pp)):
            else 
              pa:=[op(pa),pp+symmetry*eval(pp,[r1=r2,r2=r1])]:
              p:=expand(simplify(p-pp-symmetry*eval(pp,[r1=r2,r2=r1]))):
            end if:
          end do:
          pa:=[op(pa),p]:
        end if:
        pa:=eval(pa,dummy=0):
        for pp in pa do
          if nops(pa)=1 or (not pp=0) then
            invertpolytools:-invertrimonomial(pp,symmetry,nonsingular,`if`(pp=0,h,NULL)):
            if pp=0 then [eval(invertpolytools:-invertrimonomial(pp,-1,false,h)[1],c=b)+%[1],0]: end if:
            eval(%,[Block1=-2*arctanh(r12/(r1+r2)), Block2=-2*arctanh((r1-r2)/r12), TailPlus=invertpolytools:-tailzero, TailMinus=invertpolytools:-tailzero]);
            simplify(L()(%[1])+%[2]-pp):
            if (simplify(%)=0) then
              ts:=ts+%%%:
            else error("Faulty inversion: ",pp,%%%,simplify(%)):
            end if:
          end if:
        end do:
      map(zz->collect(zz,[rz,r12],simplify),ts);
      if op(2,%)=0 then collect(op(1,%),[op(indets(ts,name) minus {r1,r2,r12,r12}),arctanh, Block1, Block2],factor@simplify):
      else collect(op(1,%)+Linv(op(2,%)),[op(indets(ts,name) minus {r1,r2,r12,r12}),arctanh, Block1, Block2,Linv],factor@simplify):
      end if:
      return eval(%,[Block1=-2*ln(r1+r2+r12),Block2=Sum(Sum(((1/2)*a)^(2*n+1)*GAMMA((1/2)*k+1+2*n)*(-(1/2)*sqrt(2)*d)^k/(GAMMA((1/2)*k+3/2+n)*GAMMA(n+3/2)), k = 0 .. infinity), n = 0 .. infinity), TailPlus=invertpolytools:-getTailPlus, TailMinus=invertpolytools:-getTailMinus]);
    end proc:



    ####################################################################################
    ####################################################################################
    ##              Compare two expressions wrt their series expansions               ##
    ####################################################################################
    ####################################################################################

    getser := proc (f, v, TM)
      local ser, jj; jj := 5;
      ser := series(f+dummy*v^(TM+2),v,TM+2);
      while op(-1,ser) < TM+2 and jj < 4*TM do jj := jj+2;
      ser := series(f+dummy*v^(TM+jj),v,TM+jj) end do; ser := eval(series(ser+dummy*v^TM,v,TM),dummy = 0);
      if not type(ser,series) then print(`(Compare debug output) --- Not a series: `,ser,v,TM,`  ---  `) end if;
      return [expand(convert(ser,polynom)), O(v^convert(op(-1,ser),name))] 
    end proc;

    compare := proc (rs, ls := 0, TM := 10, ivars := [], {onlyeven := {}, onlyodd := {}} )
      local v, vars, tser, otail;
      vars := ivars;
      otail := 1;
      tser := expand(eval(rs-ls,[infinity = TM+2, Sum = add]));
      if % = 0 then return 0 end if;
      if vars = [] then vars := `minus`(indets(%,name),{E, Pi, Z, c, infinity}) end if;
      for v in vars while true do
        getser(tser,v,TM);
        tser := %[1];
        otail := otail*`%%`[2];
      end do;
      tser := expand(eval(tser,ln = `@`(zz -> simplify(zz,symbolic),ln)));
      if 0 < nops(onlyeven) then print(`Considering only even powers of: `,op(onlyeven),`  Warning: csgn and signum functions will be ignored.`);
        for v in onlyeven while true do tser := eval(add(coeff(eval(tser,[op(map(zz -> ln(zz) = ll[zz],vars)), csgn = (yy -> 1), signum = (yy -> 1)]),v,2*ii)*v^(2*ii),ii = 0 .. 1/2*TM)
        +add(coeff(eval(tser,[op(map(zz -> ln(zz) = ll[zz],vars)), csgn = (yy -> 1), signum = (yy -> 1)]),v,-2*ii)*v^(-2*ii),ii = 0 .. 1/2*TM),map(zz -> ll[zz] = ln(zz),vars));
        end do;
      end if;
      if 0 < nops(onlyodd) then print(`Considering only odd powers of: `,op(onlyodd),`  Warning: csgn and signum functions will be ignored.`);
        for v in onlyodd while true do tser := eval(add(coeff(eval(tser,[op(map(zz -> ln(zz) = ll[zz],vars)), csgn = (yy -> 1), signum = (yy -> 1)]),v,2*ii+1)*v^(2*ii+1)
        ,ii = 0 .. 1/2*TM)+add(coeff(eval(tser,[op(map(zz -> ln(zz) = ll[zz],vars)), csgn = (yy -> 1), signum = (yy -> 1)]),v,-2*ii-1)*v^(-2*ii-1),ii = 0 .. 1/2*TM),
        map(zz -> ll[zz] = ln(zz),vars))
        end do;
      end if;
      if ivars = [] then vars := sort([op(vars)],(va, vb) -> evalb(nops({seq(coeff(eval(tser,[op(map(zz -> ln(zz) = ll[zz],vars)), csgn = (yyy -> 1), signum = (yyy -> 1)]),va,ii),
      ii = -TM .. TM)}) <= nops({seq(coeff(eval(tser,[op(map(zz -> ln(zz) = ll[zz],vars)), csgn = (yyy -> 1), signum = (yyy -> 1)]),vb,ii),ii = -TM .. TM)}))) else vars := ivars end if;
      tser := collect(tser,vars);
      return tser+otail;
    end proc;

    ####################################################################################
    ####################################################################################
    ##                                Summation tools                                 ##
    ####################################################################################
    ####################################################################################

    # Turn a hypergeometric function into a sum 
    hyper2sum := proc (expr, indinp, varinp, opts:=[])
      local inds:=indinp, ind:=inds[1], var;
      if is(expr,polynom) then return expr; end if:
      if op(0,expr)=`^` and op(0,op(1,expr))=`+` and is(op(2,expr),posint) then
          try
            binomexpand(expr,index=ind,`if`(is(op(2,expr),name),breakoff,NULL)):
            return %;
          end try:
      end if:

      if not varinp=auto then var:=varinp:
      elif nops(indets(expr,name))=1 then var:=op(1,indets(expr,name));
      end if:

      ind:=op(1,inds);                                                                   # Select index as first of constructed list

      # If pure hypergeom, turn directly into sum.
      if op(0,expr) = hypergeom or op(0,expr) = Hypergeom then
        if op(0,op(3,expr)) = `^` then op(1,op(3,expr))^(op(2,op(3,expr))*ind) else op(3,expr)^ind; end if; 
        return Sum(mul(pochhammer(op(1,expr)[ii],ind),ii = 1 .. nops(op(1,expr)))/mul(pochhammer(op(2,expr)[ii],ind),ii = 1 .. nops(op(2,expr)))*%/ind!,ind = 0 .. infinity);
      end if;

      # Determine variable: If necessary and possible, guess.
      if not varinp=auto then var:=varinp;
      else
        indets(expr,name):
        if nops(%)=0 then return expr;                                                # No names -> No expansion necessary.
        elif nops(%)=1 then var:=op(1,%);                                             # Expression containing a single name
        elif is(expr,function) and nops(expr)=1 then var:=op(1,expr);                 # Function of a single argument containing multiple names
        elif nops(% minus {i,j,k,n,m,l})=1 then var:=op(1,% minus {i,j,k,n,m,l});     # Expression of a single non-typical-index name
        else
          sort([op(map(yy->[opm1(yy),op0(yy)],map(zz->series(expr,zz,10),indets(expr,name))))],(x,y)->x[1]>y[1]);
          if %[1][1]>6 and %[2][1]<6 then var:=%[1][2];                               # If there is only one variable with a long series expansion, take that one.
          else
            WARNING(convert(cat("In expression ",convert(expr,string),": Not sure which variable to expand in, please specify as 3rd argument: convert(t,sum,variable(s),{index})."),name));
            var:=op(1,%);                                                             # Wild guess.
          end if:
        end if:
      end if:

      # If no hypergeoms are involved: apply convert\FormalPowerSeries.
      if nops(map(zz->op(0,zz),indets(expr,function)) intersect {`hypergeom`,`Hypergeom`})=0 then
        eval(convert(eval(expr,var=dummy),FormalPowerSeries,dummy,ind,op(opts)),dummy=var);
        if not (%=expr) then return %; end if;                                         # Full FPS successful
        collect(expr,map(zz->`if`(var in indets(zz,name),zz,NULL),indets(%)));         # Collect in var-dependent stuff
        if op(0,%) = `+` then                                                          # Map onto summands
          return map(zz->hyper2sum(zz,indinp,varinp,opts),%);
        end if:
  #      if op(0,expr)=`*` and then                                                    # Mapping onto products: currently disabled.
  #        map(zz->`if`(is(op(2,zz),posint),seq(op(1,zz),ii=1..op(2,zz)),op(1,zz)^op(2,zz)),factors(expr)[2]);
  #        return factors(expr)[1]*mul(hyper2sum(%[ii],[inds[ii]],varinp,opts),ii=1..nops(%));
  #      end if:
      end if:

      # Otherwise, if necessary, map to hypergeoms.
      if not op(0,expr) in {`hypergeom`,`Hypergeom`} then
        return eval(expr,hypergeom=(zz->hyper2sum(zz,indinp))@hypergeom);
      end if;

      return expr;

    end proc;

    # Expand sums
    Expand:=proc(s)
      eval(s,Sum=Int);
      IntegrationTools:-Expand(%);
      IntegrationTools:-Expand(%);
      IntegrationTools:-Expand(%); # Sometimes it doesn't expand everything in the first round, so repeat.
      return combinepowers(eval(%,Int=Sum));
    end proc:

    # combine powers such as (x^n)^2 into x^(2n).
    combinepowers:=proc(t)
      map(xx->xx[1]=xx[1]/xx[2]*combine(xx[2]),map(zz->[zz,map(yy->`if`(is(yy,name) or is(yy,`^`),yy,1),zz)],indets(t,`*`)));
      return subs(%,t);
     # return eval(t,map(zz->zz=combine(zz),indets(t,`^`)));
    end proc:

    # Apply fkt to argument deepest or specified sum and Sum in s
    summap:=proc(mapfkt,expr,expind:=`any`)
      indets(expr,'specfunc(anything,{Sum,sum})');
      map(zz->[zz,`if`(op(0,op(2,zz))=`=`,lhs(op(2,zz)),op(2,zz)),nops(indets(zz,function))],[op(%)]); #[zz,index,c-depth]
    
      if expind=`any` then sort(%,(x,y)->x[3]<y[3])[1][1];                                          # Deepest sum
      else ListTools:-Search(expind,map(op2,%)):
         if %=0 then ERROR("No summation with that index found!"); else %%[%][1]; end if;       # Sum with given index
      end if:
      return subs(%=op0(%)(mapfkt(op1(%)),op2(%)),expr);
    end proc:



    ####################################################################################
    ####################################################################################
    ##                                   GAMMA tools                                  ##
    ####################################################################################
    ####################################################################################

    gsimplify:=x->simplify(simplify(x,GAMMA));
    gchange:=(x,y)->x=gsimplify(x/y)*y;
    gsplit:=proc(t) # Take the gamma or pochhammer with the largest argument, split it in 2.
      local tosplit, fkts:=[op(map(zz->`if`(op(0,zz) in {GAMMA,factorial,pochhammer},zz,NULL),indets(t,function)))];
    
      if nops(fkts)=0 then return t: end if:
      map(zz->max(map(yy->coeff(op(-1,zz),yy,1),indets(t,name))),fkts); # Choose the term with the largest multiplicity of any variable
      if max(%)>0 then tosplit:=fkts[ListTools[Search](max(%),%)];
      else map(zz->op(-1,zz),fkts):
        tosplit:=fkts[ListTools[Search](max(%),%)];
      end if:
    
      if op(0,tosplit)='GAMMA' then
        op(1,tosplit);
        gchange(tosplit,GAMMA(%/2)*GAMMA(%/2+1/2)/(2^lcoeff(%,op(1,indets(%,name))))^(-op(1,%/lcoeff(%,op(1,indets(%,name))))));
        return eval(t,%);
      elif op(0,tosplit)='factorial' then
        op(1,tosplit);
        if is(%,odd) assuming op(map(zz->zz::posint,indets(%,name))) then
          gchange(tosplit,pochhammer(1,(%-1)/2)*pochhammer(3/2,(%-1)/2)/(2^lcoeff(%,op(1,indets(%,name))))^(-op(1,%/lcoeff(%,op(1,indets(%,name))))));
        else
          gchange(tosplit,(%/2)!*pochhammer(1/2,%/2)/(2^lcoeff(%,op(1,indets(%,name))))^(-op(1,%/lcoeff(%,op(1,indets(%,name))))));
        end if:
        return eval(t,lhs(%)=trimpoch(rhs(%)));
      elif op(0,tosplit)='pochhammer' then
        op(2,tosplit);
        gchange(tosplit,pochhammer(op(1,tosplit)/2,%/2)*pochhammer(op(1,tosplit)/2+1/2,%/2)/(2^lcoeff(%,op(1,indets(%,name))))
                        ^(-%/lcoeff(%,op(1,indets(%,name)))));
        return eval(t,lhs(%)=trimpoch(rhs(%)));
      end if:
    end proc:

    symplify:=proc(s)
      return simplify(s,symbolic):
    end proc:

    ratplot:=proc(term,opt0:=NULL,opt1:=NULL,opt2:=NULL,opt3:=NULL,opt4:=NULL,opt5:=NULL,opt6:=NULL,opt7:=NULL,opt8:=NULL,opt9:=NULL)
      local alpharange:=0.001..Pi-0.001,thetarange:=0.001..Pi-0.001,opts;
      opts:=[opt0,opt1,opt2,opt3,opt4,opt5,opt6,opt7,opt8,opt9];
      map(zz->`if`(op(0,zz)=`=` and lhs(zz)=alpha,zz,NULL),opts);   # alpha range given?
      if nops(%)=0 then opts:=[alpha=alpharange,op(opts)]; end if;  # If not, append.
      map(zz->`if`(op(0,zz)=`=` and lhs(zz)=theta,zz,NULL),opts);   # theta range given?
      if nops(%)=0 then opts:=[op(opts),theta=thetarange]; end if;  # If not, append.
      map(zz->`if`(op(0,zz)=`=` and lhs(zz)=axes,zz,NULL),opts);    # axes given?
      if nops(%)=0 then opts:=[op(opts),axes=boxed]; end if;        # If not, append.

      return plot3d(eval(eval(eval(eval(term,[Sum=add,infinity=20]),[r1 = sqrt(1/2)*r*sqrt(1+cos(alpha)), r2 = sqrt(1/2)*r*sqrt(1-cos(alpha)), r12 = r*sqrt(1-sin(alpha)*cos(theta))])
      ,[a = cos(alpha), d = sqrt(1-sin(alpha)*cos(theta)), w = sin(alpha)*cos(theta), v = cos(theta)
      ,s = (1/2)*r*(sqrt(2+2*cos(alpha))+sqrt(2-2*cos(alpha))), t = (1/2)*r*(sqrt(2+2*cos(alpha))-sqrt(2-2*cos(alpha))), u = r*sqrt(1-sin(alpha)*cos(theta))]),[r=1,Z=2]),op(opts));
    end proc:


   # poch:=(x,y)->pochhammer(x,y);
   # F:=(x,y,z)->hypergeom(x,y,z);


    ####################################################################################
    ####################################################################################
    ##                              Sequence Identificator                            ##
    ####################################################################################
    ####################################################################################

    
    IdSeqMod := module()
      export IdSeq_inner, StoredSeq:=[seq([],ii=1..100)]:
      local maxifactor,nrifactors,firstoccurrence,trend,getpoch,removedenom,getminusonepowers,bestdenomfactor,possiblefactors,promisingfactors,bestpochs,possiblepochs,
            ifacpattern,score,penalty,polyans:

      maxifactor:=x->eval(max({op(map(zz->op(1,zz),ifactors(x)[2]))}),[-infinity=1]):
      nrifactors:=x->`+`(op(map(zz->`if`(zz[1]=2,NULL,zz[2]),ifactors(x)[2]))):

      firstoccurrence:=proc(f,clist) # find first occurrence of the prime factor f in the coefficients in clist.
        local factorslist:=map(yy->{op(map(zz->op(1,zz),ifactors(yy)[2]))},clist):   # [{prime factors}]
        map(zz->`if`(f in zz,1,0),factorslist):
        return ListTools:-Search(1,%);
      end proc:

      polyans:=proc(iclist,d:=nops(iclist)-2,{debug:=false,minusfactor:=0})
        local c,f:=1,clist:=map(expand,iclist),ans:=add(c[ii]*n^ii,ii=0..d), eqs:={}, i, mf:

        # Identify powers of 2
        round(trend(clist,power2)):
        clist:=[seq(clist[ii]/2^(%*ii),ii=1..nops(clist))];
        if %%>0 then f:=f*2^(%%*n); else f:=f/2^(-%%*n); end if:
        if debug then print(`In polyans: Power of 2 is `, 2^(%%%*n)); end if:
     
        if minusfactor=0 then 
          # Identify powers of -1
          mf:=getminusonepowers(clist):
          f:=f*mf;
          clist:=[seq(eval(mf,n=ii)*clist[ii],ii=1..nops(clist))]:
          if debug then print(`In polyans: Power of -1 is `, mf); end if:
        else
          f:=f*minusfactor;
          clist:=[seq(eval(minusfactor,n=ii)*clist[ii],ii=1..nops(clist))]:
        end if:

        for i from 1 to nops(clist) do
          eval(ans,n=i)=(clist[i]);
          eqs:=eqs union {%}:
        end do:
        if debug then print(`In polyans: Equations to solve: `, eqs); end if:  
        [solve(eqs,{seq(c[ii],ii=0..d)})];
          if debug then print(`In polyans: Solution:`, %); end if:
        if not %=[] then return f*factor(eval(ans,%[1]));
        elif minusfactor=0 then return polyans(iclist,d,convert("minusfactor",name)=`if`(mf=1,(-1)^n,1)); # Check opposite minus,too.
        else return 1; end if:
      end proc:

      trend:=proc(clist,lookat:='all')
        local llist:
        if lookat='all' then
          llist:=clist:
        elif lookat='nrfacs' then
          llist:=map(nops,map(yy->map(zz->`if`(op(1,zz)>5,`$`(op(1,zz),op(2,zz)),NULL),ifactors(yy)[2]),clist));
        elif lookat='power2' then
          llist:=map(xx->`if`(nops(xx)<2,0,xx[2]),map(zz->[zz,op(map(yy->`if`(yy[1]=2,yy[2],NULL),ifactors(zz)[2]))],clist));
        end if:
        return evalf(coeff(CurveFitting[LeastSquares]([seq([ii,llist[ii]],ii=1..nops(llist))],x,curve=a*x+b),x,1));
      end proc:
      
      # Find a pochhammer which has the factor f as its last term
      getpoch:=proc(f) # f=(x*n+y)
        #if degree(f,n)=0 then return op([pochhammer(1,f),pochhammer(1/2,(f+1)/2),pochhammer(1+f/4-floor(f/4),floor(f/4))]); end if;
        if degree(f,n)=0 then return NULL; end if;
        eval(expand(f/lcoeff(f,n)),n=0); # y/x
        if is(%,negint) then return (n-1)!;
        else return pochhammer(%+1,n);
        end if:
      end proc:
      
      removedenom:=proc(iclist,dbu:=`nodebug`,{ISdebug:=false,lin_vs_poch:=3/2})
        global previous_denom_facs:
        local nrloops:=0,bestfac,c:=1,clist:=iclist,db:=false,chosenfacs:={},bestfacnew:
        if dbu=`debug` then db:=true: end if:
        if db then print(`removedenom called:`, clist, `isdebug`=ISdebug, `lin vs poch`=lin_vs_poch); end if;
        while max(map(maxifactor@denom,clist))>2 do
          if nrloops>20 then break; end if:
          nrloops:=nrloops+1;
      
          if db then print(`removedenom loop Nr.`, nrloops,` calling bestdenomfactor with: `,map(ifactor@denom,clist)); end if;
          bestfac:=bestdenomfactor(map(denom,clist),convert("ISdebug,",name)=ISdebug,convert("lin_vs_poch",name)=lin_vs_poch);
          if ISdebug then print(`In removedenom, factor chosen: `,bestfac): end if:
          previous_denom_facs:=[op(previous_denom_facs),bestfac]:
          if db then print(`removedenom chose factor: `,bestfac); end if;
          [seq(clist[ii]*eval(bestfac,n=ii),ii=1..nops(clist))]:
           clist:=%; c:=c/bestfac;
          if not op(0,bestfac)=`pochhammer` and 
                 expand(eval(bestfac,n=n+1)) in chosenfacs and expand(eval(bestfac,n=n+2)) in chosenfacs then
            if db then print(`In removedenom: Consecutive linear factors detected: `, seq(expand(eval(bestfac,n=n+ii)),ii=0..2));
            return removedenom(iclist,dbu,convert("ISdebug",name)=ISdebug,convert("lin_vs_poch",name)=lin_vs_poch+1);
          end if:
          end if:
          if not type(bestfac,numeric) then chosenfacs:=chosenfacs union {bestfac}: end if;
      
        end do:

        # Identify powers of 2
        round(trend(clist,power2)):
        clist:=[seq(clist[ii]/2^(%*ii),ii=1..nops(clist))];
        if %%>0 then c:=c*2^(%%*n); else c:=c/2^(-%%*n); end if:
        c:=collect(c,[pochhammer,factorial],simplify);
      
        return [c,clist,chosenfacs];
      end proc:
      
      getminusonepowers:=proc(clist)
        [seq(abs(signum(clist[ii])/2-signum(clist[ii-1])/2),ii=2..nops(clist))];
        [seq(abs(signum(clist[ii])/2+signum(clist[ii-1])/2),ii=2..nops(clist))];
        `+`(op(%%))/nops(clist)-`+`(op(%))/nops(clist);
        if abs(%)<0.1 and nops(clist)>10 then return getminusonepowers(clist[2..-1]): #If uncertain, ignore first clist element
        elif %<0 then return 1;
        else return (-1)^n;
        end if:
      end proc:

      IdSeq_inner:=proc(iclist,firstindexeq:=n=1,dbu:=`nodebug`,{pvl:=1.6,getserious:=false})
        # Higher pvl makes linear denom factors less likely.
        # getserious triggers strongly extended detection of numer pochhammers.
        global previous_numer_facs:=[], previous_denom_facs:=[]:
        local ef:=iclist[-1]/op(1,iclist[-1]*dummy), # extra factor other than fraction of integers
              clist:=map(zz->zz/ef,iclist),
              remgamma,c,gg,polysol,db:=false,chosendenomfacs:={}:
        if dbu=`debug` then db:=true: end if:
      
        # After leading zeroes are gone, initialize:
        c:=ef*clist[1];
        clist:=map(zz->zz/c,iclist);
        if db then print(clist); end if;
      
        # Identify up to 10 numerator GAMMAs
        for gg from 1 to 10 do

          c:=c*clist[1];
          clist:=[seq(clist[ii]/clist[1],ii=1..nops(clist))];

          removedenom(clist,ISdebug=db,`lin_vs_poch`=pvl);
          c:=c*%[1];
          clist:=%%[2];
          chosendenomfacs:=chosendenomfacs union %%%[3];
          if db then print(`IdSeq after removedenom:`,c,ifactor(clist)); end if;
          trend(clist,nrfacs);
          if abs(%)<0.5 then
            if db then print (`Attempting polynomial ansatz...`, clist); end if;
            polysol:=polyans(clist);
            c:=c*polysol;
            clist:=[seq(clist[ii]/eval(polysol,n=ii),ii=1..nops(clist))];
            #print(`Breakoff condition, pos 1: `, clist,max(map(abs,{op(clist)})));
            if max(map(abs,{op(clist)}))=1 then return [c,clist]; end if; # DONE!
          end if:

          c:=c*clist[1];
          clist:=[seq(clist[ii]/clist[1],ii=1..nops(clist))];

          if db then print(`IdSeq calling bestpochs:`, map(numer,clist)); end if;
          bestpochs(map(numer,clist),serious=getserious);
          if db then print(`IdSeq bestpochs:`,%); end if;
          remgamma:=%[1][1];
          clist:=[seq((clist[ii]/eval(remgamma,n=ii)),ii=1..nops(clist))];
          c:=c*remgamma:
          if db then print(`IdSeq after removing pochhammer `,remgamma,` from numerator: New c:`,c,ifactor(clist)); end if;
          previous_numer_facs:=[op(previous_numer_facs),remgamma]:

          trend(clist,nrfacs);
          if abs(%)<0.5 then
            if db then print (`Attempting polynomial ansatz...`,clist); end if;
            polysol:=polyans(clist);
            c:=c*polysol;
            clist:=[seq(clist[ii]/eval(polysol,n=ii),ii=1..nops(clist))];
            #print(`Breakoff condition, pos 2: `,clist,max(map(abs,{op(clist)})));
            if max(map(abs,{op(clist)}))=1 then return [c, clist]; end if; # DONE!
          end if:
      
        end do:
      
        [c, clist];
        return %;
      end proc:

      bestdenomfactor:=proc(clist,{debug:=false,lin_vs_poch:=3/2})
        local fo,pf,allifacs,c_patterns,fac_patterns,fac_nonoverlaps,pochfac_patterns,pf_nonoverlaps,ff,cp,ci,pp,ip,scores:
        map(maxifactor,clist);
        if max(%)>88-max(20,nops(clist)) then return max(%); end if; # Too large: Just give up.
        if trend(eval(%,2=1))<=0.1 then return max(%); end if; # Pretty certainly just a constant. # Adjustment: vary around 0. (0.2 is too large.)
        fo:=firstoccurrence(max(%),%):
        if debug then print(`In bestdenomfactor: possible linear factors are: `,possiblefactors([max(%%),fo])); end if;
        pf:=ListTools:-MakeUnique(possiblefactors([max(%%),fo])); # Possible linear factors producing the largest maxifactor
        pf:=[op(map(zz->`if`(is(eval(zz,n=1),nonposint),NULL,zz),pf)),op(map(getpoch,pf))]:   # Add all corresponding pochhammers
      #  pf:=[op(map(zz->`if`(is(eval(zz,n=0),prime) or (eval(zz,n=0) in {0,1}),zz,NULL),pf)),op(map(getpoch,pf))]:
        if debug then print(`In bestdenomfactor: possible factors are: `,pf); end if:
        scores:=score(pf,clist,convert("lin_vs_poch",name)=lin_vs_poch):
        if debug then print(`bestfac scores: `,%); end if;
        if debug then print(`bestfac scores: `,%); end if;
        return scores[1][1];
      end proc:
      
      possiblefactors:=proc(fo)  # Input: [prime factor,first occurrence]
        local prfac:=fo[1], firstocc:=fo[2]:
        [x,2*x+1,4*x+1,4*x+3]; # Possible factors
        [op(map(zz->eval(zz,x=n+solve(prfac=zz,x)-firstocc),%))];
      #  ,op(map(zz->eval(zz,x=n+solve(2*prfac=zz,x)-firstocc),%))
      #  ,op(map(zz->eval(zz,x=n+solve(3*prfac=zz,x)-firstocc),%))
      #  ,op(map(zz->eval(zz,x=n+solve(4*prfac=zz,x)-firstocc),%))
      #  map(zz->`if`(is(coeff(zz,n,1)/4,integer) and is(coeff(zz,n,0)/4,integer),zz/4,zz),%):
      #  map(zz->`if`(is(coeff(zz,n,1)/3,integer) and is(coeff(zz,n,0)/3,integer),zz/3,zz),%):
      #  map(zz->`if`(is(coeff(zz,n,1)/2,integer) and is(coeff(zz,n,0)/2,integer),zz/2,zz),%):
        map(zz->`if`(coeff(zz,n,0)/lcoeff(zz,n)>80,NULL,zz),%):
        return ListTools:-MakeUnique([prfac,op(%)]):
      end proc:
      
      promisingfactors:=proc(clist)
        local factorslist:=map(yy->map(zz->op(1,zz),ifactors(yy)[2]),clist),   # [[prime factors]]
              flatfaclist:=ListTools:-Flatten(factorslist),
              minfac:=10,nroc:=2,
              oclist:=[op(map(zz->[zz,ListTools:-Occurrences(zz,flatfaclist)],{op(flatfaclist)}))],  # [ [primefactor,#Occurrences] ]
              pf:=map(zz->`if`(zz[1]>minfac and zz[2]>nroc,zz[1],NULL),oclist);
        if nops(pf)>3 then return pf; end if:
        pf:=map(zz->`if`(zz[1]>4 and zz[2]>nroc,zz[1],NULL),oclist);
        if nops(pf)>3 then return pf; end if:
        pf:=map(zz->`if`(zz[1]>6 and zz[2]>0,zz[1],NULL),oclist);
        if nops(pf)>3 then return pf; end if:
        pf:=map(zz->`if`(zz[1]>2 and zz[2]>0,zz[1],NULL),oclist);
        return pf;
      end proc:
      
      bestpochs:=proc(clist,{serious:=false,debug:=false})
        local flatgammas,freqgammas:
        if debug then print(`bestpochs called with `,clist,` serious`=serious); end if:
        if max(map(maxifactor,clist))<3 then return [[1,1]]; end if;
        if serious then
          [op({seq(op(map(zz->`if`(2<zz[1] and zz[1]<4*ii+33,[zz[1],ii],NULL),ifactors(clist[ii])[2])),ii=1..nops(clist))})]:
          ListTools:-MakeUnique(map(op@possiblepochs,%)):
          score(%,clist):
          return %[1..min(10,nops(%))];
        else
          promisingfactors(clist);  # look for probably-not-sum prime factor (use multiple occurrence as indicator)
          map(zz->[zz,firstoccurrence(zz,clist)],%);
          flatgammas:=ListTools:-Flatten(map(possiblepochs,%));
          # Count how often each possible poch is predicted.
          freqgammas:=sort([op(map(zz->[zz,ListTools:-Occurrences(zz,flatgammas)],{op(flatgammas)}))],(x,y)->x[2]>y[2]);
          if freqgammas[1][2]-freqgammas[1][2]>3 then return freqgammas:
          else
            [seq(`if`(freqgammas[ii][2]>1,freqgammas[ii][1],NULL),ii=1..nops(freqgammas))]:
            if nops(map(zz->`if`(penalty(zz)>0,NULL,zz),%))>0 then return score(%,clist): # If there's at least one without penalty left
            else return bestpochs(clist,convert("serious",name),convert("debug",name)=debug):   
            end if:
          end if:
        end if:
      end proc:

      possiblepochs:=proc(fo)  # Input: [prime factor,first occurrence]
        local prfac:=fo[1], firstocc:=fo[2]:
        # Possible pochhammers, corresponding first-occurrence factor
        [[pochhammer(x+1,n),x+n],[pochhammer(x/2+1,n),2*n+x],[pochhammer(x/4+1,n),4*n+x]];
        map(zz->eval(zz[1],x=solve(prfac=eval(zz[2],n=firstocc),x)),%);
        if op(1,op(1,%))<0 then return %[2..-1]; else return eval(%,pochhammer(0,n)=(n-1)!); end if; # avoid trying pochhammer(0,n) etc
      end proc:
      
      ifacpattern:=proc(clist,allifacs) # List of Nr. occurrences of factor in each coeff, for each ifactor in allifacs.
        local ii,ifp,ff:
        ifp:=map(zz->map(yy->0,clist),allifacs):
        for ii from 1 to nops(clist) do
          for ff in ifactors(clist[ii])[2] do
            ListTools:-Search(ff[1],allifacs):
            if %>0 then ifp[%][ii]:=ff[2]: end if:
          end do:
        end do:
        return(ifp):
      end proc:

      score:=proc(pf,clist,{lin_vs_poch:=3/2}) # Input: pf: List of possible (pochhammer / linear) factors. clist: List of coeffs.
                            # Returns: [[factor, score]] (lower is better)
        local allifacs,ifacpattern_c,ifacpattern_p,scores:=[],pp:
        allifacs:=sort(ListTools:-MakeUnique([op(map(yy->`if`(yy[1]=2 or yy[1]>4*nops(clist)+33,NULL,yy[1]),
                                                                                   map(zz->op(ifactors(zz)[2]),clist)))
                                             # ,seq(ithprime(ii),ii=2..6)
                                              ]),`>`);
        ifacpattern_c:=ifacpattern(clist,allifacs);
        for pp in pf do
                [seq(eval(pp,n=ii),ii=1..nops(clist))]:
          if nops(indets(%,function))>0 then break; end if; # GAMMAs in predicted coefficients => pochhammer too large, skip.
          ifacpattern_p:=ifacpattern(%,allifacs);
          `+`(seq(`+`(op(map(abs,ifacpattern_c[ii]-ifacpattern_p[ii])))*allifacs[ii],ii=1..nops(allifacs)));
          scores:=[op(scores),[pp,%]]:
        end do:
      
        scores:=map(zz->[zz[1],zz[2]+penalty(zz[1])],scores);
        # Possible adjustment: change the scaling of the linear factors.
        scores:=map(zz->[zz[1],`if`(op(0,zz[1]) in {`pochhammer`,`factorial`},1,lin_vs_poch)*zz[2]],scores);
        scores:=sort(scores,(x,y)->x[2]<y[2]);
        return scores:
      end proc:
      
      penalty:=proc(pp) # From the numbers of previous instances of pp being chosen, give a penalty to the pp score.
        global previous_numer_facs, previous_denom_facs:
        ListTools:-Occurrences(pp,previous_numer_facs):
        ListTools:-Occurrences(pp,previous_denom_facs):
        return max(%%,%)*20; # Adjustment: Give stronger/weaker penalties.
      end proc:

    end module: # IdSeqMod

    IdSeq := proc(clist,firstindexeq:=n=1,{poch_vs_lin:=1.6,serious:=false,tryall:=false,showall:=false})
      local indexname,firstindex,ser,pl,c,gotit:=false,starttime,pvlvalues:=ListTools:-MakeUnique([poch_vs_lin,1.6,4,10,1,1.3,2]):

      if op(0,firstindexeq)=`=` then indexname:=lhs(firstindexeq); firstindex:=rhs(firstindexeq);
      elif type(firstindexeq,name) then indexname:=firstindexeq; firstindex:=1;
          else indexname:=n; firstindex:=firstindexeq;
      end if;

      # Remove leading zeroes to avoid division by 0
      [ListTools:-SearchAll(0,clist)]:
      if nops(%)>0 then
        return IdSeq(clist[%[-1]+1..nops(clist)],indexname=firstindex+%[-1],convert("poch_vs_lin",name)=poch_vs_lin
                     ,convert("serious",name)=serious,convert("tryall",name)=tryall);
      end if;
    
      # try all the options      
      for ser in {serious,true} do
        for pl in pvlvalues do
          starttime:=time[real]():
          IdSeqMod:-IdSeq_inner(clist,firstindexeq,pvl=pl,`getserious`=ser);
          if {op(%[2])}={1} then
            c:=%[1]:
            gotit:=true:
            if tryall or showall then print(`poch vs lin`=pl,`getserious`=ser,` was successful. Time:`,time[real]()-starttime); end if:
            if not tryall then break: end if:
          else
            if tryall or showall then print(`poch vs lin`=pl,`getserious`=ser,` failed. Time:`,time[real]()-starttime); end if:
          end if:
        end do:
        if gotit and (not tryall) then break: end if:
      end do:
    
      if gotit then
        eval(c,n=indexname-(firstindex-1));
        eval(trimpochfac(%));
        collect(%,[pochhammer,factorial],factor@simplify);
        return %:
      elif nops(clist)>6 and firstindex<5 then # Test ignoring first few list elements.
        return IdSeq(clist[2..nops(clist)],indexname=firstindex+1,convert("poch_vs_lin",name)=poch_vs_lin
                     ,convert("serious",name)=serious,convert("tryall",name)=tryall);
      
      else
        return `FAIL`;
      end if:
    end proc:

    # Use IdSeq to identify series with numerical coefficients.
    IdSer:=proc(ser,ind:=n)
      local var,poly,e,minind,maxind,c,ii,lowind,deglist:
      if is(ser,series) then var:=op(0,ser);
      else var:=sort(map(vv->[vv,nops(map(zz->degree(zz,vv),{op(expand(ser))}))],[op(indets(ser))]),(x,y)->x[2]>y[2])[1][1]: # choose the var with most different powers.
      end if:
      poly:=sort(convert(ser,polynom),var,tdeg,ascending);
      deglist:=map(zz->degree(zz,var),[op(poly)]);        # (Sorted) list of degrees
      e:=IdSeq(deglist,ind=0);
      e:=coeff(e,ind)*ind + (eval(e,ind=0) mod 2);   # New exponent with minimal constant addition
      minind:=solve(e = deglist[1],ind);
      maxind:=solve(e = deglist[-1],ind);
      [seq(coeff(poly,var,eval(e,ind=ii)),ii=minind..maxind)]; # List of coefficients
      c:=IdSeq(%,ind=minind);
      for ii from maxind to minind by -1 do # Make sure sum evaluation works, start summation at higher index if necessary.
        try eval(c,ind=ii);
          lowind:=ii:             # lowind: Lowest index for which evaluation works.
        catch:
        end try:
      end do:
      Sum(c*var^e,ind=lowind..infinity);
      return convert(series(ser-%,var,degree(convert(ser,polynom))-2),polynom)+%;
    end proc:

    # Append an element to seqind-th sequence.
    app2seq:=proc(se,seqind:=1)
      if is(se,list) then
        IdSeqMod:-StoredSeq[seqind]:=[op(IdSeqMod:-StoredSeq[seqind]),op(se)]:
      else
        IdSeqMod:-StoredSeq[seqind]:=[op(IdSeqMod:-StoredSeq[seqind]),se]:
      end if:
    end proc:

    # Retrieve stored sequence
    getseq:=proc(seqind:=1)
      return IdSeqMod:-StoredSeq[seqind]:
    end proc:

    # Set stored sequence
    setseq:=proc(s::list,seqind:=1)
      IdSeqMod:-StoredSeq[seqind]:=s:
    end proc:

    # Set stored sequence
    resetseq:=proc(seqind:=1,{all::boolean := false})
      local ii;
      IdSeqMod:-StoredSeq[seqind]:=[]:
      for ii from 1 to nops(IdSeqMod:-StoredSeq) do
        IdSeqMod:-StoredSeq[ii]:=[]:
      end do:
    end proc:

   ## Attempts to reproduce a list of numbers, iclist, using a polynomial of degree d.
   # polyansatz := proc(iclist,d:=nops(iclist)-2)
   #   return IdSeqMod:-polyans(iclist,d);
   # end proc:
    
    # Simplification of multi-angle trigonometric expressions - first applies multi-angle, then half-angle formulas.
    multiangle:=proc(s,{`symbolic`:=false})
      local constfac,intfac,x,n,keepfloor:=`if`(symbolic,0,1):
      if not (op(0,s) in {`sin`,`cos`}) then
        return eval(s,[sin=(zz->multiangle(sin(zz),`if`(symbolic,convert("symbolic",name),NULL))),
                      cos=(zz->multiangle(cos(zz),`if`(symbolic,convert("symbolic",name),NULL)))]) end if:
      if not (op(0,op(1,s))=`*` and `or`(op(map(zz->is(zz,constant),{op(op(1,s))})))) then return s; end if;
      constfac:=op(1,map(zz->`if`(is(zz,constant),zz,NULL),[op(op(1,s))]));
      if constfac=1 then return s: end if:
      intfac:=numer(constfac):
      x:=op(1,s)/intfac:
      if is(intfac-1,posint) then
        n:=intfac:
        #print("Multi: ",n);
        if op(0,s)=`sin` then
          if is(n,odd) then
            #print("Returning: ",convert((-1)^((n-1)/2)*ChebyshevT(n,(sin(x))),elementary));
            return multiangle(convert((-1)^((n-1)/2)*ChebyshevT(n,sin(x)),elementary),`if`(symbolic,convert("symbolic",name),NULL));
          elif is(n,even) then
            #print("Returning: ",convert((-1)^(n/2-1)*cos(x)*ChebyshevU(n-1,(sin(x))),elementary));
            return multiangle(convert((-1)^(n/2-1)*cos(x)*ChebyshevU(n-1,sin(x)),elementary),`if`(symbolic,convert("symbolic",name),NULL));
          end if:
        elif op(0,s)=`cos` then
          if is(n,odd) then
            #print("Returning: ",convert((-1)^((n-1)/2)*cos(x)*ChebyshevU(n-1,sin(x)),elementary));
            return multiangle(convert((-1)^((n-1)/2)*cos(x)*ChebyshevU(n-1,sin(x)),elementary),`if`(symbolic,convert("symbolic",name),NULL));
          elif is(n,even) then
            #print("Returning: ",convert((-1)^(n/2)*ChebyshevT(n,(sin(x))),elementary));
            return multiangle(convert((-1)^(n/2)*ChebyshevT(n,sin(x)),elementary),`if`(symbolic,convert("symbolic",name),NULL));
          end if:
        end if:    
      end if:
      if is(denom(constfac),even) then
        x:=op(1,s)*2:
        if op(0,s)=`sin` then
          return ((-1)^floor(x/(2*Pi)))^keepfloor*sqrt((1-multiangle(cos(x),`if`(symbolic,convert("symbolic",name),NULL)))/2);
        elif op(0,s)=`cos` then
          return ((-1)^floor((x+Pi)/(2*Pi)))^keepfloor*sqrt((1+multiangle(cos(x),`if`(symbolic,convert("symbolic",name),NULL)))/2);
        end if:
      end if:
      return s:
    end proc:
    
    hypconvert:=proc(expr)
      return convert(convert(convert(expr,hypergeom),hypergeom,include=all,exclude=powers),hypergeom,include=radicals);
    end proc:
    
    ####################################################################################
    ####################################################################################
    ##                               Recurrence relations                             ##
    ####################################################################################
    ####################################################################################
   
    getshifts:=proc(pows,term)
      local vv,P,x,shifts:=[]:
      for vv from 1 to nops(pows) do
        eval(pows[vv][2],op(1,indets(pows[vv][2],name))=op(1,indets(pows[vv][2],name))+x)+degree(term,pows[vv][1])=pows[vv][2];
        shifts:=[op(shifts),op(1,indets(pows[vv][2],name))=op(1,indets(pows[vv][2],name))+solve(%,x)];
      end do:
      return shifts;
    end proc:

    RecRelinner:=proc(cc,term)
      local vars:={op(map(lhs,cc&>ri))}, pows, pp, rpow:=1:
      pows:=map(zz->`if`(op(1,zz) in vars,[op(1,zz),op(2,zz)],NULL),indets(term,`^`));
      for pp in pows do
        if pp[1]=r then rpow:=r^(pp[2]-2); pows:=eval(pows,pp=NULL);
        elif is(pp[2],constant) then ERROR(cat("Please provide non-constant exponent for variable ",pp[1])); end if;
      end do:
      vars minus map(zz->op(1,zz),pows) minus {r}; # Variables that were not found as powers in term
      if nops(%)>0 then ERROR(cat("Please provide non-constant exponent for variable(s) ",convert(op(%),string))); end if;
      collect(simplify(L(cc)(term)/`*`(op(map(zz->zz[1]^zz[2],pows)))),vars,distributed,yy->collect(yy,diff,factor));
      map(zz->eval(eval(zz,getshifts(pows,zz)),map(yy->yy[1]=1,pows))/rpow,%)=Coeff(rho,rpow*(`*`(op(map(zz->zz[1]^zz[2],pows)))));
    end proc:


    RecRel:=proc(cc:=rad)
       return proc(term) return RecRelinner(cc,term); end proc:
    end proc:

    nextcoeff:=proc(RR,gi)
      local coefnames,neq,nc:
      coefnames:=map(zz->`if`(op0(zz)='c',zz,NULL),indets(RR));
      map(zz->`if`(nops(map(yy->`if`(is(yy-gi,posint),yy,NULL),[op(zz)]))>0,zz,NULL),%); # Select the coeff in which gi is growing.
      if nops(%)>1 then ERROR(cat("Recurrence relation has several coefficients with incremented index ",gi)); end if;
      if nops(%)<1 then ERROR(cat("Recurrence relation has no coefficients with incremented index ",gi)); end if;
      neq:=%[1] = collect(solve(RR,%[1]),%%,factor);
      nc:=proc(prevc)
        local extranames,pc,ff:
        if rhs(prevc) = 0 then ff:=1:
        else ff:=map(zz->`if`(is(zz,function),zz,1),dummy*numer(rhs(prevc)))/map(zz->`if`(is(zz,function),zz,1),dummy*denom(rhs(prevc)));
        end if:
        extranames:=indets(rhs(prevc),name) minus indets(RR,name);
        if nops(extranames)>0 then WARNING(cat("Found names other than indices or coefficients: ",convert(extranames,string),". Setting these to 1."));
        end if;
        pc:=eval(prevc,map(zz->zz=1,extranames));
        map(zz->eval(pc,[op(indets(op1(zz)))=op(indets(op1(zz)))+op1(zz)-op1(lhs(pc)),op(indets(op2(zz)))=op(indets(op2(zz)))+op2(zz)-op2(lhs(pc))]),coefnames minus {lhs(neq)});
        eval(neq,[op(indets(op1(lhs(neq))))=op1(lhs(pc)),op(indets(op2(lhs(neq))))=op2(lhs(pc))]);
        eval(%,%%);
        if (not ff=1) then lhs(%) = factor(simplify(rhs(%)/ff))*ff; end if;
        return %;
      end proc:
      return %:
    end proc:

    
    expandsqrta:=proc(expr)
      return eval(expr,[seq(sqrt(1+sqrt(-a^2+1))^ii = ((1/2)*sqrt(2)*(sqrt(1-a)+sqrt(1+a)))^ii,ii=1..7),
      seq(sqrt(1-sqrt(-a^2+1))^ii = (abs(a)*sqrt(2)/(sqrt(1-a)+sqrt(1+a)))^ii,ii=-7..7),
      seq(1/(1+sqrt(-a^2+1))^(ii/2) = (-(1/2)*(sqrt(1-a)-sqrt(1+a))*sqrt(2)/a)^ii,ii=1..7),
      sqrt(1-a^2)=sqrt(1+a)*sqrt(1-a)]);
    end proc:
    combinesqrta:=proc(expr)
      return eval(expr,[sqrt(1+a)+sqrt(1-a) = sqrt(2)*sqrt(1+sqrt(-a^2+1)),
      sqrt(1-a)-sqrt(1+a) = -sqrt(2)*a/sqrt(1+sqrt(-a^2+1)),
      sqrt(1+a)*sqrt(1-a) = sqrt(1-a^2),
      r1+r2 = r*sqrt(1+sqrt(-a^2+1)),
      r1*r2 = (1/2)*r^2*sqrt(-a^2+1)]);
    end proc:

    
    VOP :=proc(cc:=ri) return eval(map(simplify,eval(-Z/r1-Z/r2+Y/r12,ri&>cc)),[1/sqrt(2+2*a)=1/sqrt(1+a)/sqrt(2),1/sqrt(2-2*a)=1/sqrt(1-a)/sqrt(2)]); end proc:
    VOP0:=proc(cc:=ri) return eval(map(simplify,eval(-Z/r1-Z/r2+0/r12,ri&>cc)),[1/sqrt(2+2*a)=1/sqrt(1+a)/sqrt(2),1/sqrt(2-2*a)=1/sqrt(1-a)/sqrt(2)]); end proc:
    SERR:=T(Psi[n])=-V*Psi[n-1]+E*Psi[n-2];

    ####################################################################################
    ####################################################################################
    ##                                  Lazy shortcuts                                ##
    ####################################################################################
    ####################################################################################

    opm2:=zz->op(-2,zz);
    opm1:=zz->op(-1,zz);
    op0:=zz->op(0,zz);
    op1:=zz->op(1,zz);
    op2:=zz->op(2,zz);




end module: # GiosToolsNew

LibraryTools[Save](GiosTools):
