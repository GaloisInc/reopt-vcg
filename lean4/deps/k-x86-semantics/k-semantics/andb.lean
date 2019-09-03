def andb1 : instruction :=
  definst "andb" $ do
    pattern fun (v_2697 : imm int) al => do
      v_5110 <- getRegister rax;
      v_5112 <- eval (handleImmediateWithSignExtend v_2697 8 8);
      v_5114 <- eval (bv_and (extract v_5110 56 57) (extract v_5112 0 1));
      v_5116 <- eval (bv_and (extract v_5110 56 64) v_5112);
      setRegister rax (concat (extract v_5110 0 56) v_5116);
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (mux (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (bv_and (extract v_5110 63 64) (extract v_5112 7 8)) (expression.bv_nat 1 1)) (eq (bv_and (extract v_5110 62 63) (extract v_5112 6 7)) (expression.bv_nat 1 1)))) (eq (bv_and (extract v_5110 61 62) (extract v_5112 5 6)) (expression.bv_nat 1 1)))) (eq (bv_and (extract v_5110 60 61) (extract v_5112 4 5)) (expression.bv_nat 1 1)))) (eq (bv_and (extract v_5110 59 60) (extract v_5112 3 4)) (expression.bv_nat 1 1)))) (eq (bv_and (extract v_5110 58 59) (extract v_5112 2 3)) (expression.bv_nat 1 1)))) (eq (bv_and (extract v_5110 57 58) (extract v_5112 1 2)) (expression.bv_nat 1 1)))) (eq v_5114 (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (zeroFlag v_5116);
      setRegister af undef;
      setRegister sf v_5114;
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end;
    pattern fun (v_2713 : imm int) (v_2716 : reg (bv 8)) => do
      v_5182 <- getRegister v_2716;
      v_5184 <- eval (bv_and v_5182 (handleImmediateWithSignExtend v_2713 8 8));
      setRegister (lhs.of_reg v_2716) v_5184;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (parityFlag (extract v_5184 0 8));
      setRegister af undef;
      setRegister zf (zeroFlag v_5184);
      setRegister sf (extract v_5184 0 1);
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end;
    pattern fun (v_2724 : reg (bv 8)) (v_2725 : reg (bv 8)) => do
      v_5200 <- getRegister v_2725;
      v_5201 <- getRegister v_2724;
      v_5202 <- eval (bv_and v_5200 v_5201);
      setRegister (lhs.of_reg v_2725) v_5202;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (parityFlag (extract v_5202 0 8));
      setRegister af undef;
      setRegister zf (zeroFlag v_5202);
      setRegister sf (extract v_5202 0 1);
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end;
    pattern fun (v_2732 : imm int) (v_2735 : reg (bv 8)) => do
      v_5228 <- getRegister v_2735;
      v_5230 <- eval (bv_and v_5228 (handleImmediateWithSignExtend v_2732 8 8));
      setRegister (lhs.of_reg v_2735) v_5230;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (parityFlag (extract v_5230 0 8));
      setRegister zf (zeroFlag v_5230);
      setRegister af undef;
      setRegister sf (extract v_5230 0 1);
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end;
    pattern fun (v_2744 : reg (bv 8)) (v_2743 : reg (bv 8)) => do
      v_5246 <- getRegister v_2743;
      v_5247 <- getRegister v_2744;
      v_5248 <- eval (bv_and v_5246 v_5247);
      setRegister (lhs.of_reg v_2743) v_5248;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (parityFlag (extract v_5248 0 8));
      setRegister zf (zeroFlag v_5248);
      setRegister af undef;
      setRegister sf (extract v_5248 0 1);
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end;
    pattern fun (v_2719 : Mem) (v_2720 : reg (bv 8)) => do
      v_9292 <- getRegister v_2720;
      v_9293 <- evaluateAddress v_2719;
      v_9294 <- load v_9293 1;
      v_9295 <- eval (bv_and v_9292 v_9294);
      setRegister (lhs.of_reg v_2720) v_9295;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (parityFlag (extract v_9295 0 8));
      setRegister zf (zeroFlag v_9295);
      setRegister af undef;
      setRegister sf (extract v_9295 0 1);
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end;
    pattern fun (v_2701 : imm int) (v_2703 : Mem) => do
      v_10869 <- evaluateAddress v_2703;
      v_10870 <- load v_10869 1;
      v_10872 <- eval (bv_and v_10870 (handleImmediateWithSignExtend v_2701 8 8));
      store v_10869 v_10872 1;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (parityFlag (extract v_10872 0 8));
      setRegister af undef;
      setRegister zf (zeroFlag v_10872);
      setRegister sf (extract v_10872 0 1);
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end;
    pattern fun (v_2707 : reg (bv 8)) (v_2706 : Mem) => do
      v_10884 <- evaluateAddress v_2706;
      v_10885 <- load v_10884 1;
      v_10886 <- getRegister v_2707;
      v_10887 <- eval (bv_and v_10885 v_10886);
      store v_10884 v_10887 1;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (parityFlag (extract v_10887 0 8));
      setRegister af undef;
      setRegister zf (zeroFlag v_10887);
      setRegister sf (extract v_10887 0 1);
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end
