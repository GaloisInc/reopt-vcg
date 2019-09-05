def sarw1 : instruction :=
  definst "sarw" $ do
    pattern fun cl (v_3176 : reg (bv 16)) => do
      v_6956 <- getRegister rcx;
      v_6958 <- eval (bv_and (extract v_6956 56 64) (expression.bv_nat 8 31));
      v_6959 <- eval (eq v_6958 (expression.bv_nat 8 0));
      v_6960 <- eval (notBool_ v_6959);
      v_6961 <- getRegister v_3176;
      v_6964 <- eval (ashr (concat v_6961 (expression.bv_nat 1 0)) (concat (expression.bv_nat 9 0) v_6958));
      v_6965 <- eval (extract v_6964 0 16);
      v_6968 <- getRegister zf;
      v_6974 <- getRegister sf;
      v_6981 <- getRegister pf;
      v_6987 <- eval (bit_and v_6960 undef);
      v_6988 <- getRegister of;
      v_6995 <- getRegister cf;
      v_6999 <- getRegister af;
      setRegister (lhs.of_reg v_3176) v_6965;
      setRegister af (bit_or v_6987 (bit_and v_6959 (eq v_6999 (expression.bv_nat 1 1))));
      setRegister cf (bit_or (bit_and v_6960 (isBitSet v_6964 16)) (bit_and v_6959 (eq v_6995 (expression.bv_nat 1 1))));
      setRegister of (bit_and (notBool_ (eq v_6958 (expression.bv_nat 8 1))) (bit_or v_6987 (bit_and v_6959 (eq v_6988 (expression.bv_nat 1 1)))));
      setRegister pf (bit_or (bit_and v_6960 (parityFlag (extract v_6964 8 16))) (bit_and v_6959 (eq v_6981 (expression.bv_nat 1 1))));
      setRegister sf (bit_or (bit_and v_6960 (isBitSet v_6964 0)) (bit_and v_6959 (eq v_6974 (expression.bv_nat 1 1))));
      setRegister zf (bit_or (bit_and v_6960 (eq v_6965 (expression.bv_nat 16 0))) (bit_and v_6959 (eq v_6968 (expression.bv_nat 1 1))));
      pure ()
    pat_end;
    pattern fun (v_3183 : imm int) (v_3180 : reg (bv 16)) => do
      v_7011 <- eval (bv_and (handleImmediateWithSignExtend v_3183 8 8) (expression.bv_nat 8 31));
      v_7012 <- eval (eq v_7011 (expression.bv_nat 8 0));
      v_7013 <- eval (notBool_ v_7012);
      v_7014 <- getRegister v_3180;
      v_7017 <- eval (ashr (concat v_7014 (expression.bv_nat 1 0)) (concat (expression.bv_nat 9 0) v_7011));
      v_7018 <- eval (extract v_7017 0 16);
      v_7021 <- getRegister zf;
      v_7027 <- getRegister sf;
      v_7034 <- getRegister pf;
      v_7040 <- eval (bit_and v_7013 undef);
      v_7041 <- getRegister of;
      v_7048 <- getRegister cf;
      v_7052 <- getRegister af;
      setRegister (lhs.of_reg v_3180) v_7018;
      setRegister af (bit_or v_7040 (bit_and v_7012 (eq v_7052 (expression.bv_nat 1 1))));
      setRegister cf (bit_or (bit_and v_7013 (isBitSet v_7017 16)) (bit_and v_7012 (eq v_7048 (expression.bv_nat 1 1))));
      setRegister of (bit_and (notBool_ (eq v_7011 (expression.bv_nat 8 1))) (bit_or v_7040 (bit_and v_7012 (eq v_7041 (expression.bv_nat 1 1)))));
      setRegister pf (bit_or (bit_and v_7013 (parityFlag (extract v_7017 8 16))) (bit_and v_7012 (eq v_7034 (expression.bv_nat 1 1))));
      setRegister sf (bit_or (bit_and v_7013 (isBitSet v_7017 0)) (bit_and v_7012 (eq v_7027 (expression.bv_nat 1 1))));
      setRegister zf (bit_or (bit_and v_7013 (eq v_7018 (expression.bv_nat 16 0))) (bit_and v_7012 (eq v_7021 (expression.bv_nat 1 1))));
      pure ()
    pat_end;
    pattern fun (v_3185 : reg (bv 16)) => do
      v_8558 <- getRegister v_3185;
      v_8560 <- eval (ashr (concat v_8558 (expression.bv_nat 1 0)) (expression.bv_nat 17 1));
      v_8561 <- eval (extract v_8560 0 16);
      setRegister (lhs.of_reg v_3185) v_8561;
      setRegister af undef;
      setRegister cf (isBitSet v_8560 16);
      setRegister of bit_zero;
      setRegister pf (parityFlag (extract v_8560 8 16));
      setRegister sf (isBitSet v_8560 0);
      setRegister zf (zeroFlag v_8561);
      pure ()
    pat_end;
    pattern fun cl (v_3165 : Mem) => do
      v_13983 <- evaluateAddress v_3165;
      v_13984 <- load v_13983 2;
      v_13986 <- getRegister rcx;
      v_13988 <- eval (bv_and (extract v_13986 56 64) (expression.bv_nat 8 31));
      v_13990 <- eval (ashr (concat v_13984 (expression.bv_nat 1 0)) (concat (expression.bv_nat 9 0) v_13988));
      v_13991 <- eval (extract v_13990 0 16);
      store v_13983 v_13991 2;
      v_13993 <- eval (eq v_13988 (expression.bv_nat 8 0));
      v_13994 <- eval (notBool_ v_13993);
      v_13997 <- getRegister zf;
      v_14003 <- getRegister sf;
      v_14010 <- getRegister pf;
      v_14016 <- eval (bit_and v_13994 undef);
      v_14017 <- getRegister of;
      v_14024 <- getRegister cf;
      v_14028 <- getRegister af;
      setRegister af (bit_or v_14016 (bit_and v_13993 (eq v_14028 (expression.bv_nat 1 1))));
      setRegister cf (bit_or (bit_and v_13994 (isBitSet v_13990 16)) (bit_and v_13993 (eq v_14024 (expression.bv_nat 1 1))));
      setRegister of (bit_and (notBool_ (eq v_13988 (expression.bv_nat 8 1))) (bit_or v_14016 (bit_and v_13993 (eq v_14017 (expression.bv_nat 1 1)))));
      setRegister pf (bit_or (bit_and v_13994 (parityFlag (extract v_13990 8 16))) (bit_and v_13993 (eq v_14010 (expression.bv_nat 1 1))));
      setRegister sf (bit_or (bit_and v_13994 (isBitSet v_13990 0)) (bit_and v_13993 (eq v_14003 (expression.bv_nat 1 1))));
      setRegister zf (bit_or (bit_and v_13994 (eq v_13991 (expression.bv_nat 16 0))) (bit_and v_13993 (eq v_13997 (expression.bv_nat 1 1))));
      pure ()
    pat_end;
    pattern fun (v_3168 : imm int) (v_3169 : Mem) => do
      v_14038 <- evaluateAddress v_3169;
      v_14039 <- load v_14038 2;
      v_14042 <- eval (bv_and (handleImmediateWithSignExtend v_3168 8 8) (expression.bv_nat 8 31));
      v_14044 <- eval (ashr (concat v_14039 (expression.bv_nat 1 0)) (concat (expression.bv_nat 9 0) v_14042));
      v_14045 <- eval (extract v_14044 0 16);
      store v_14038 v_14045 2;
      v_14047 <- eval (eq v_14042 (expression.bv_nat 8 0));
      v_14048 <- eval (notBool_ v_14047);
      v_14051 <- getRegister zf;
      v_14057 <- getRegister sf;
      v_14064 <- getRegister pf;
      v_14070 <- eval (bit_and v_14048 undef);
      v_14071 <- getRegister of;
      v_14078 <- getRegister cf;
      v_14082 <- getRegister af;
      setRegister af (bit_or v_14070 (bit_and v_14047 (eq v_14082 (expression.bv_nat 1 1))));
      setRegister cf (bit_or (bit_and v_14048 (isBitSet v_14044 16)) (bit_and v_14047 (eq v_14078 (expression.bv_nat 1 1))));
      setRegister of (bit_and (notBool_ (eq v_14042 (expression.bv_nat 8 1))) (bit_or v_14070 (bit_and v_14047 (eq v_14071 (expression.bv_nat 1 1)))));
      setRegister pf (bit_or (bit_and v_14048 (parityFlag (extract v_14044 8 16))) (bit_and v_14047 (eq v_14064 (expression.bv_nat 1 1))));
      setRegister sf (bit_or (bit_and v_14048 (isBitSet v_14044 0)) (bit_and v_14047 (eq v_14057 (expression.bv_nat 1 1))));
      setRegister zf (bit_or (bit_and v_14048 (eq v_14045 (expression.bv_nat 16 0))) (bit_and v_14047 (eq v_14051 (expression.bv_nat 1 1))));
      pure ()
    pat_end;
    pattern fun (v_3172 : Mem) => do
      v_14620 <- evaluateAddress v_3172;
      v_14621 <- load v_14620 2;
      v_14623 <- eval (ashr (concat v_14621 (expression.bv_nat 1 0)) (expression.bv_nat 17 1));
      v_14624 <- eval (extract v_14623 0 16);
      store v_14620 v_14624 2;
      setRegister af undef;
      setRegister cf (isBitSet v_14623 16);
      setRegister of bit_zero;
      setRegister pf (parityFlag (extract v_14623 8 16));
      setRegister sf (isBitSet v_14623 0);
      setRegister zf (zeroFlag v_14624);
      pure ()
    pat_end
