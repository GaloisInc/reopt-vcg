def rcrw1 : instruction :=
  definst "rcrw" $ do
    pattern fun cl (v_2548 : reg (bv 16)) => do
      v_4701 <- getRegister cf;
      v_4704 <- getRegister v_2548;
      v_4706 <- getRegister rcx;
      v_4710 <- eval (urem (concat (expression.bv_nat 9 0) (bv_and (extract v_4706 56 64) (expression.bv_nat 8 31))) (expression.bv_nat 17 17));
      v_4712 <- eval (rorHelper (concat (mux (eq v_4701 (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0)) v_4704) (uvalueMInt v_4710) 0);
      v_4714 <- eval (extract v_4710 9 17);
      v_4715 <- eval (eq v_4714 (expression.bv_nat 8 1));
      v_4724 <- eval (eq v_4714 (expression.bv_nat 8 0));
      v_4727 <- getRegister of;
      setRegister (lhs.of_reg v_2548) (extract v_4712 1 17);
      setRegister of (mux (bit_or (bit_and v_4715 (notBool_ (eq (eq (extract v_4712 1 2) (expression.bv_nat 1 1)) (eq (extract v_4712 2 3) (expression.bv_nat 1 1))))) (bit_and (notBool_ v_4715) (bit_or (bit_and (notBool_ v_4724) undef) (bit_and v_4724 (eq v_4727 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (extract v_4712 0 1);
      pure ()
    pat_end;
    pattern fun (v_2551 : imm int) (v_2553 : reg (bv 16)) => do
      v_4738 <- getRegister cf;
      v_4741 <- getRegister v_2553;
      v_4746 <- eval (urem (concat (expression.bv_nat 9 0) (bv_and (handleImmediateWithSignExtend v_2551 8 8) (expression.bv_nat 8 31))) (expression.bv_nat 17 17));
      v_4748 <- eval (rorHelper (concat (mux (eq v_4738 (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0)) v_4741) (uvalueMInt v_4746) 0);
      v_4750 <- eval (extract v_4746 9 17);
      v_4751 <- eval (eq v_4750 (expression.bv_nat 8 1));
      v_4760 <- eval (eq v_4750 (expression.bv_nat 8 0));
      v_4763 <- getRegister of;
      setRegister (lhs.of_reg v_2553) (extract v_4748 1 17);
      setRegister of (mux (bit_or (bit_and v_4751 (notBool_ (eq (eq (extract v_4748 1 2) (expression.bv_nat 1 1)) (eq (extract v_4748 2 3) (expression.bv_nat 1 1))))) (bit_and (notBool_ v_4751) (bit_or (bit_and (notBool_ v_4760) undef) (bit_and v_4760 (eq v_4763 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (extract v_4748 0 1);
      pure ()
    pat_end;
    pattern fun $0x1 (v_2557 : reg (bv 16)) => do
      v_4774 <- getRegister cf;
      v_4776 <- eval (mux (eq v_4774 (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      v_4777 <- getRegister v_2557;
      v_4778 <- eval (concat v_4776 v_4777);
      v_4781 <- eval (add (bitwidthMInt v_4776) 16);
      v_4782 <- eval (sub v_4781 1);
      v_4786 <- eval (add (lshr v_4778 1) (concat (extract v_4778 v_4782 v_4781) (mi v_4782 0)));
      setRegister (lhs.of_reg v_2557) (extract v_4786 1 17);
      setRegister of (mux (notBool_ (eq (eq (extract v_4786 1 2) (expression.bv_nat 1 1)) (eq (extract v_4786 2 3) (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (extract v_4786 0 1);
      pure ()
    pat_end;
    pattern fun cl (v_2537 : Mem) => do
      v_13964 <- evaluateAddress v_2537;
      v_13965 <- getRegister cf;
      v_13968 <- load v_13964 2;
      v_13970 <- getRegister rcx;
      v_13974 <- eval (urem (concat (expression.bv_nat 9 0) (bv_and (extract v_13970 56 64) (expression.bv_nat 8 31))) (expression.bv_nat 17 17));
      v_13976 <- eval (rorHelper (concat (mux (eq v_13965 (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0)) v_13968) (uvalueMInt v_13974) 0);
      store v_13964 (extract v_13976 1 17) 2;
      v_13980 <- eval (extract v_13974 9 17);
      v_13981 <- eval (eq v_13980 (expression.bv_nat 8 1));
      v_13990 <- eval (eq v_13980 (expression.bv_nat 8 0));
      v_13993 <- getRegister of;
      setRegister of (mux (bit_or (bit_and v_13981 (notBool_ (eq (eq (extract v_13976 1 2) (expression.bv_nat 1 1)) (eq (extract v_13976 2 3) (expression.bv_nat 1 1))))) (bit_and (notBool_ v_13981) (bit_or (bit_and (notBool_ v_13990) undef) (bit_and v_13990 (eq v_13993 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (extract v_13976 0 1);
      pure ()
    pat_end;
    pattern fun (v_2541 : imm int) (v_2540 : Mem) => do
      v_14002 <- evaluateAddress v_2540;
      v_14003 <- getRegister cf;
      v_14006 <- load v_14002 2;
      v_14011 <- eval (urem (concat (expression.bv_nat 9 0) (bv_and (handleImmediateWithSignExtend v_2541 8 8) (expression.bv_nat 8 31))) (expression.bv_nat 17 17));
      v_14013 <- eval (rorHelper (concat (mux (eq v_14003 (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0)) v_14006) (uvalueMInt v_14011) 0);
      store v_14002 (extract v_14013 1 17) 2;
      v_14017 <- eval (extract v_14011 9 17);
      v_14018 <- eval (eq v_14017 (expression.bv_nat 8 1));
      v_14027 <- eval (eq v_14017 (expression.bv_nat 8 0));
      v_14030 <- getRegister of;
      setRegister of (mux (bit_or (bit_and v_14018 (notBool_ (eq (eq (extract v_14013 1 2) (expression.bv_nat 1 1)) (eq (extract v_14013 2 3) (expression.bv_nat 1 1))))) (bit_and (notBool_ v_14018) (bit_or (bit_and (notBool_ v_14027) undef) (bit_and v_14027 (eq v_14030 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (extract v_14013 0 1);
      pure ()
    pat_end
