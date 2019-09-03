def testb1 : instruction :=
  definst "testb" $ do
    pattern fun (v_2378 : imm int) al => do
      v_3970 <- getRegister rax;
      v_3972 <- eval (handleImmediateWithSignExtend v_2378 8 8);
      v_3974 <- eval (bv_and (extract v_3970 56 57) (extract v_3972 0 1));
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (mux (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (bv_and (extract v_3970 63 64) (extract v_3972 7 8)) (expression.bv_nat 1 1)) (eq (bv_and (extract v_3970 62 63) (extract v_3972 6 7)) (expression.bv_nat 1 1)))) (eq (bv_and (extract v_3970 61 62) (extract v_3972 5 6)) (expression.bv_nat 1 1)))) (eq (bv_and (extract v_3970 60 61) (extract v_3972 4 5)) (expression.bv_nat 1 1)))) (eq (bv_and (extract v_3970 59 60) (extract v_3972 3 4)) (expression.bv_nat 1 1)))) (eq (bv_and (extract v_3970 58 59) (extract v_3972 2 3)) (expression.bv_nat 1 1)))) (eq (bv_and (extract v_3970 57 58) (extract v_3972 1 2)) (expression.bv_nat 1 1)))) (eq v_3974 (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af undef;
      setRegister zf (zeroFlag (bv_and (extract v_3970 56 64) v_3972));
      setRegister sf v_3974;
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end;
    pattern fun (v_2394 : imm int) (v_2396 : reg (bv 8)) => do
      v_4039 <- getRegister v_2396;
      v_4041 <- eval (bv_and v_4039 (handleImmediateWithSignExtend v_2394 8 8));
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (parityFlag (extract v_4041 0 8));
      setRegister af undef;
      setRegister zf (zeroFlag v_4041);
      setRegister sf (extract v_4041 0 1);
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end;
    pattern fun (v_2400 : reg (bv 8)) (v_2401 : reg (bv 8)) => do
      v_4052 <- getRegister v_2401;
      v_4053 <- getRegister v_2400;
      v_4054 <- eval (bv_and v_4052 v_4053);
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (parityFlag (extract v_4054 0 8));
      setRegister af undef;
      setRegister zf (zeroFlag v_4054);
      setRegister sf (extract v_4054 0 1);
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end;
    pattern fun (v_2383 : imm int) (v_2382 : Mem) => do
      v_8772 <- evaluateAddress v_2382;
      v_8773 <- load v_8772 1;
      v_8775 <- eval (bv_and v_8773 (handleImmediateWithSignExtend v_2383 8 8));
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (parityFlag (extract v_8775 0 8));
      setRegister af undef;
      setRegister zf (zeroFlag v_8775);
      setRegister sf (extract v_8775 0 1);
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end;
    pattern fun (v_2387 : reg (bv 8)) (v_2386 : Mem) => do
      v_8786 <- evaluateAddress v_2386;
      v_8787 <- load v_8786 1;
      v_8788 <- getRegister v_2387;
      v_8789 <- eval (bv_and v_8787 v_8788);
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (parityFlag (extract v_8789 0 8));
      setRegister af undef;
      setRegister zf (zeroFlag v_8789);
      setRegister sf (extract v_8789 0 1);
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end
