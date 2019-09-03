def rolb1 : instruction :=
  definst "rolb" $ do
    pattern fun cl (v_2571 : reg (bv 8)) => do
      v_4809 <- getRegister rcx;
      v_4811 <- eval (bv_and (extract v_4809 56 64) (expression.bv_nat 8 31));
      v_4812 <- eval (eq v_4811 (expression.bv_nat 8 0));
      v_4813 <- eval (notBool_ v_4812);
      v_4814 <- getRegister v_2571;
      v_4816 <- eval (rolHelper v_4814 (uvalueMInt v_4811) 0);
      v_4818 <- eval (eq (extract v_4816 7 8) (expression.bv_nat 1 1));
      v_4820 <- getRegister cf;
      v_4825 <- eval (eq v_4811 (expression.bv_nat 8 1));
      v_4833 <- getRegister of;
      setRegister (lhs.of_reg v_2571) v_4816;
      setRegister of (mux (bit_or (bit_and v_4825 (notBool_ (eq (eq (extract v_4816 0 1) (expression.bv_nat 1 1)) v_4818))) (bit_and (notBool_ v_4825) (bit_or (bit_and v_4813 undef) (bit_and v_4812 (eq v_4833 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux (bit_or (bit_and v_4813 v_4818) (bit_and v_4812 (eq v_4820 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2574 : imm int) (v_2576 : reg (bv 8)) => do
      v_4844 <- eval (bv_and (handleImmediateWithSignExtend v_2574 8 8) (expression.bv_nat 8 31));
      v_4845 <- eval (eq v_4844 (expression.bv_nat 8 0));
      v_4846 <- eval (notBool_ v_4845);
      v_4847 <- getRegister v_2576;
      v_4849 <- eval (rolHelper v_4847 (uvalueMInt v_4844) 0);
      v_4851 <- eval (eq (extract v_4849 7 8) (expression.bv_nat 1 1));
      v_4853 <- getRegister cf;
      v_4858 <- eval (eq v_4844 (expression.bv_nat 8 1));
      v_4866 <- getRegister of;
      setRegister (lhs.of_reg v_2576) v_4849;
      setRegister of (mux (bit_or (bit_and v_4858 (notBool_ (eq (eq (extract v_4849 0 1) (expression.bv_nat 1 1)) v_4851))) (bit_and (notBool_ v_4858) (bit_or (bit_and v_4846 undef) (bit_and v_4845 (eq v_4866 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux (bit_or (bit_and v_4846 v_4851) (bit_and v_4845 (eq v_4853 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun $0x1 (v_2580 : reg (bv 8)) => do
      v_4876 <- getRegister v_2580;
      v_4881 <- eval (add (extract (shl v_4876 1) 0 8) (concat (expression.bv_nat 7 0) (extract v_4876 0 1)));
      v_4882 <- eval (extract v_4881 7 8);
      setRegister (lhs.of_reg v_2580) v_4881;
      setRegister of (mux (notBool_ (eq (eq (extract v_4881 0 1) (expression.bv_nat 1 1)) (eq v_4882 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf v_4882;
      pure ()
    pat_end;
    pattern fun cl (v_2560 : Mem) => do
      v_14091 <- evaluateAddress v_2560;
      v_14092 <- load v_14091 1;
      v_14093 <- getRegister rcx;
      v_14095 <- eval (bv_and (extract v_14093 56 64) (expression.bv_nat 8 31));
      v_14097 <- eval (rolHelper v_14092 (uvalueMInt v_14095) 0);
      store v_14091 v_14097 1;
      v_14099 <- eval (eq v_14095 (expression.bv_nat 8 0));
      v_14100 <- eval (notBool_ v_14099);
      v_14102 <- eval (eq (extract v_14097 7 8) (expression.bv_nat 1 1));
      v_14104 <- getRegister cf;
      v_14109 <- eval (eq v_14095 (expression.bv_nat 8 1));
      v_14117 <- getRegister of;
      setRegister of (mux (bit_or (bit_and v_14109 (notBool_ (eq (eq (extract v_14097 0 1) (expression.bv_nat 1 1)) v_14102))) (bit_and (notBool_ v_14109) (bit_or (bit_and v_14100 undef) (bit_and v_14099 (eq v_14117 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux (bit_or (bit_and v_14100 v_14102) (bit_and v_14099 (eq v_14104 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2564 : imm int) (v_2563 : Mem) => do
      v_14126 <- evaluateAddress v_2563;
      v_14127 <- load v_14126 1;
      v_14129 <- eval (bv_and (handleImmediateWithSignExtend v_2564 8 8) (expression.bv_nat 8 31));
      v_14131 <- eval (rolHelper v_14127 (uvalueMInt v_14129) 0);
      store v_14126 v_14131 1;
      v_14133 <- eval (eq v_14129 (expression.bv_nat 8 0));
      v_14134 <- eval (notBool_ v_14133);
      v_14136 <- eval (eq (extract v_14131 7 8) (expression.bv_nat 1 1));
      v_14138 <- getRegister cf;
      v_14143 <- eval (eq v_14129 (expression.bv_nat 8 1));
      v_14151 <- getRegister of;
      setRegister of (mux (bit_or (bit_and v_14143 (notBool_ (eq (eq (extract v_14131 0 1) (expression.bv_nat 1 1)) v_14136))) (bit_and (notBool_ v_14143) (bit_or (bit_and v_14134 undef) (bit_and v_14133 (eq v_14151 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux (bit_or (bit_and v_14134 v_14136) (bit_and v_14133 (eq v_14138 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end
