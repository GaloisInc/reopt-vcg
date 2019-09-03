def sarq1 : instruction :=
  definst "sarq" $ do
    pattern fun cl (v_3086 : reg (bv 64)) => do
      v_7705 <- getRegister rcx;
      v_7707 <- eval (bv_and (extract v_7705 56 64) (expression.bv_nat 8 63));
      v_7708 <- eval (eq v_7707 (expression.bv_nat 8 0));
      v_7709 <- eval (notBool_ v_7708);
      v_7710 <- getRegister v_3086;
      v_7711 <- eval (concat v_7710 (expression.bv_nat 1 0));
      v_7717 <- eval (ashr (mi (bitwidthMInt v_7711) (svalueMInt v_7711)) (uvalueMInt (concat (expression.bv_nat 57 0) v_7707)));
      v_7721 <- getRegister cf;
      v_7729 <- getRegister sf;
      v_7734 <- eval (bit_and v_7709 undef);
      v_7735 <- getRegister af;
      v_7740 <- eval (extract v_7717 0 64);
      v_7743 <- getRegister zf;
      v_7778 <- getRegister pf;
      v_7785 <- getRegister of;
      setRegister (lhs.of_reg v_3086) v_7740;
      setRegister of (mux (bit_and (notBool_ (eq v_7707 (expression.bv_nat 8 1))) (bit_or v_7734 (bit_and v_7708 (eq v_7785 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (mux (bit_or (bit_and v_7709 (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (extract v_7717 63 64) (expression.bv_nat 1 1)) (eq (extract v_7717 62 63) (expression.bv_nat 1 1)))) (eq (extract v_7717 61 62) (expression.bv_nat 1 1)))) (eq (extract v_7717 60 61) (expression.bv_nat 1 1)))) (eq (extract v_7717 59 60) (expression.bv_nat 1 1)))) (eq (extract v_7717 58 59) (expression.bv_nat 1 1)))) (eq (extract v_7717 57 58) (expression.bv_nat 1 1)))) (eq (extract v_7717 56 57) (expression.bv_nat 1 1)))) (bit_and v_7708 (eq v_7778 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (mux (bit_or (bit_and v_7709 (eq v_7740 (expression.bv_nat 64 0))) (bit_and v_7708 (eq v_7743 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af (mux (bit_or v_7734 (bit_and v_7708 (eq v_7735 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (mux (bit_or (bit_and v_7709 (eq (extract v_7717 0 1) (expression.bv_nat 1 1))) (bit_and v_7708 (eq v_7729 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux (bit_or (bit_and v_7709 (eq (extract v_7717 64 65) (expression.bv_nat 1 1))) (bit_and v_7708 (eq v_7721 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_3087 : imm int) (v_3091 : reg (bv 64)) => do
      v_7799 <- eval (bv_and (handleImmediateWithSignExtend v_3087 8 8) (expression.bv_nat 8 63));
      v_7800 <- eval (eq v_7799 (expression.bv_nat 8 0));
      v_7801 <- eval (notBool_ v_7800);
      v_7802 <- getRegister v_3091;
      v_7803 <- eval (concat v_7802 (expression.bv_nat 1 0));
      v_7809 <- eval (ashr (mi (bitwidthMInt v_7803) (svalueMInt v_7803)) (uvalueMInt (concat (expression.bv_nat 57 0) v_7799)));
      v_7813 <- getRegister cf;
      v_7821 <- getRegister sf;
      v_7826 <- eval (bit_and v_7801 undef);
      v_7827 <- getRegister af;
      v_7832 <- eval (extract v_7809 0 64);
      v_7835 <- getRegister zf;
      v_7870 <- getRegister pf;
      v_7877 <- getRegister of;
      setRegister (lhs.of_reg v_3091) v_7832;
      setRegister of (mux (bit_and (notBool_ (eq v_7799 (expression.bv_nat 8 1))) (bit_or v_7826 (bit_and v_7800 (eq v_7877 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (mux (bit_or (bit_and v_7801 (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (extract v_7809 63 64) (expression.bv_nat 1 1)) (eq (extract v_7809 62 63) (expression.bv_nat 1 1)))) (eq (extract v_7809 61 62) (expression.bv_nat 1 1)))) (eq (extract v_7809 60 61) (expression.bv_nat 1 1)))) (eq (extract v_7809 59 60) (expression.bv_nat 1 1)))) (eq (extract v_7809 58 59) (expression.bv_nat 1 1)))) (eq (extract v_7809 57 58) (expression.bv_nat 1 1)))) (eq (extract v_7809 56 57) (expression.bv_nat 1 1)))) (bit_and v_7800 (eq v_7870 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (mux (bit_or (bit_and v_7801 (eq v_7832 (expression.bv_nat 64 0))) (bit_and v_7800 (eq v_7835 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af (mux (bit_or v_7826 (bit_and v_7800 (eq v_7827 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (mux (bit_or (bit_and v_7801 (eq (extract v_7809 0 1) (expression.bv_nat 1 1))) (bit_and v_7800 (eq v_7821 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux (bit_or (bit_and v_7801 (eq (extract v_7809 64 65) (expression.bv_nat 1 1))) (bit_and v_7800 (eq v_7813 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun $0x1 (v_3098 : reg (bv 64)) => do
      v_7892 <- getRegister v_3098;
      v_7893 <- eval (concat v_7892 (expression.bv_nat 1 0));
      v_7897 <- eval (ashr (mi (bitwidthMInt v_7893) (svalueMInt v_7893)) 1);
      v_7900 <- eval (extract v_7897 0 64);
      setRegister (lhs.of_reg v_3098) v_7900;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (parityFlag (extract v_7897 56 64));
      setRegister zf (zeroFlag v_7900);
      setRegister af undef;
      setRegister sf (extract v_7897 0 1);
      setRegister cf (extract v_7897 64 65);
      pure ()
    pat_end;
    pattern fun (v_3094 : reg (bv 64)) => do
      v_9926 <- getRegister v_3094;
      v_9927 <- eval (concat v_9926 (expression.bv_nat 1 0));
      v_9931 <- eval (ashr (mi (bitwidthMInt v_9927) (svalueMInt v_9927)) 1);
      v_9938 <- eval (extract v_9931 0 64);
      setRegister (lhs.of_reg v_3094) v_9938;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (parityFlag (extract v_9931 56 64));
      setRegister af (mux undef (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (zeroFlag v_9938);
      setRegister sf (mux (eq (extract v_9931 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux (eq (extract v_9931 64 65) (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_3094 : reg (bv 64)) => do
      v_9949 <- getRegister v_3094;
      v_9950 <- eval (concat v_9949 (expression.bv_nat 1 0));
      v_9954 <- eval (ashr (mi (bitwidthMInt v_9950) (svalueMInt v_9950)) 1);
      v_9957 <- eval (extract v_9954 0 64);
      setRegister (lhs.of_reg v_3094) v_9957;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (parityFlag (extract v_9954 56 64));
      setRegister af undef;
      setRegister zf (zeroFlag v_9957);
      setRegister sf (extract v_9954 0 1);
      setRegister cf (extract v_9954 64 65);
      pure ()
    pat_end;
    pattern fun cl (v_3070 : Mem) => do
      v_17169 <- evaluateAddress v_3070;
      v_17170 <- load v_17169 8;
      v_17171 <- eval (concat v_17170 (expression.bv_nat 1 0));
      v_17175 <- getRegister rcx;
      v_17177 <- eval (bv_and (extract v_17175 56 64) (expression.bv_nat 8 63));
      v_17180 <- eval (ashr (mi (bitwidthMInt v_17171) (svalueMInt v_17171)) (uvalueMInt (concat (expression.bv_nat 57 0) v_17177)));
      v_17181 <- eval (extract v_17180 0 64);
      store v_17169 v_17181 8;
      v_17183 <- eval (eq v_17177 (expression.bv_nat 8 0));
      v_17184 <- eval (notBool_ v_17183);
      v_17188 <- getRegister cf;
      v_17196 <- getRegister sf;
      v_17203 <- getRegister zf;
      v_17208 <- eval (bit_and v_17184 undef);
      v_17209 <- getRegister af;
      v_17244 <- getRegister pf;
      v_17251 <- getRegister of;
      setRegister of (mux (bit_and (notBool_ (eq v_17177 (expression.bv_nat 8 1))) (bit_or v_17208 (bit_and v_17183 (eq v_17251 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (mux (bit_or (bit_and v_17184 (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (extract v_17180 63 64) (expression.bv_nat 1 1)) (eq (extract v_17180 62 63) (expression.bv_nat 1 1)))) (eq (extract v_17180 61 62) (expression.bv_nat 1 1)))) (eq (extract v_17180 60 61) (expression.bv_nat 1 1)))) (eq (extract v_17180 59 60) (expression.bv_nat 1 1)))) (eq (extract v_17180 58 59) (expression.bv_nat 1 1)))) (eq (extract v_17180 57 58) (expression.bv_nat 1 1)))) (eq (extract v_17180 56 57) (expression.bv_nat 1 1)))) (bit_and v_17183 (eq v_17244 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af (mux (bit_or v_17208 (bit_and v_17183 (eq v_17209 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (mux (bit_or (bit_and v_17184 (eq v_17181 (expression.bv_nat 64 0))) (bit_and v_17183 (eq v_17203 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (mux (bit_or (bit_and v_17184 (eq (extract v_17180 0 1) (expression.bv_nat 1 1))) (bit_and v_17183 (eq v_17196 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux (bit_or (bit_and v_17184 (eq (extract v_17180 64 65) (expression.bv_nat 1 1))) (bit_and v_17183 (eq v_17188 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_3073 : imm int) (v_3074 : Mem) => do
      v_17263 <- evaluateAddress v_3074;
      v_17264 <- load v_17263 8;
      v_17265 <- eval (concat v_17264 (expression.bv_nat 1 0));
      v_17270 <- eval (bv_and (handleImmediateWithSignExtend v_3073 8 8) (expression.bv_nat 8 63));
      v_17273 <- eval (ashr (mi (bitwidthMInt v_17265) (svalueMInt v_17265)) (uvalueMInt (concat (expression.bv_nat 57 0) v_17270)));
      v_17274 <- eval (extract v_17273 0 64);
      store v_17263 v_17274 8;
      v_17276 <- eval (eq v_17270 (expression.bv_nat 8 0));
      v_17277 <- eval (notBool_ v_17276);
      v_17281 <- getRegister cf;
      v_17289 <- getRegister sf;
      v_17296 <- getRegister zf;
      v_17301 <- eval (bit_and v_17277 undef);
      v_17302 <- getRegister af;
      v_17337 <- getRegister pf;
      v_17344 <- getRegister of;
      setRegister of (mux (bit_and (notBool_ (eq v_17270 (expression.bv_nat 8 1))) (bit_or v_17301 (bit_and v_17276 (eq v_17344 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (mux (bit_or (bit_and v_17277 (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (extract v_17273 63 64) (expression.bv_nat 1 1)) (eq (extract v_17273 62 63) (expression.bv_nat 1 1)))) (eq (extract v_17273 61 62) (expression.bv_nat 1 1)))) (eq (extract v_17273 60 61) (expression.bv_nat 1 1)))) (eq (extract v_17273 59 60) (expression.bv_nat 1 1)))) (eq (extract v_17273 58 59) (expression.bv_nat 1 1)))) (eq (extract v_17273 57 58) (expression.bv_nat 1 1)))) (eq (extract v_17273 56 57) (expression.bv_nat 1 1)))) (bit_and v_17276 (eq v_17337 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af (mux (bit_or v_17301 (bit_and v_17276 (eq v_17302 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (mux (bit_or (bit_and v_17277 (eq v_17274 (expression.bv_nat 64 0))) (bit_and v_17276 (eq v_17296 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (mux (bit_or (bit_and v_17277 (eq (extract v_17273 0 1) (expression.bv_nat 1 1))) (bit_and v_17276 (eq v_17289 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux (bit_or (bit_and v_17277 (eq (extract v_17273 64 65) (expression.bv_nat 1 1))) (bit_and v_17276 (eq v_17281 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_3079 : Mem) => do
      v_18482 <- evaluateAddress v_3079;
      v_18483 <- load v_18482 8;
      v_18484 <- eval (concat v_18483 (expression.bv_nat 1 0));
      v_18488 <- eval (ashr (mi (bitwidthMInt v_18484) (svalueMInt v_18484)) 1);
      v_18489 <- eval (extract v_18488 0 64);
      store v_18482 v_18489 8;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (parityFlag (extract v_18488 56 64));
      setRegister af (mux undef (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (zeroFlag v_18489);
      setRegister sf (mux (eq (extract v_18488 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux (eq (extract v_18488 64 65) (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_3079 : Mem) => do
      v_18506 <- evaluateAddress v_3079;
      v_18507 <- load v_18506 8;
      v_18508 <- eval (concat v_18507 (expression.bv_nat 1 0));
      v_18512 <- eval (ashr (mi (bitwidthMInt v_18508) (svalueMInt v_18508)) 1);
      v_18513 <- eval (extract v_18512 0 64);
      store v_18506 v_18513 8;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (parityFlag (extract v_18512 56 64));
      setRegister af undef;
      setRegister zf (zeroFlag v_18513);
      setRegister sf (extract v_18512 0 1);
      setRegister cf (extract v_18512 64 65);
      pure ()
    pat_end
