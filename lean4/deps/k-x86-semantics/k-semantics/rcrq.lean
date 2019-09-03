def rcrq1 : instruction :=
  definst "rcrq" $ do
    pattern fun cl (v_2514 : reg (bv 64)) => do
      v_4545 <- getRegister cf;
      v_4548 <- getRegister v_2514;
      v_4550 <- getRegister rcx;
      v_4554 <- eval (urem (concat (expression.bv_nat 57 0) (bv_and (extract v_4550 56 64) (expression.bv_nat 8 63))) (expression.bv_nat 65 65));
      v_4556 <- eval (rorHelper (concat (mux (eq v_4545 (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0)) v_4548) (uvalueMInt v_4554) 0);
      v_4558 <- eval (extract v_4554 57 65);
      v_4559 <- eval (eq v_4558 (expression.bv_nat 8 1));
      v_4568 <- eval (eq v_4558 (expression.bv_nat 8 0));
      v_4571 <- getRegister of;
      setRegister (lhs.of_reg v_2514) (extract v_4556 1 65);
      setRegister of (mux (bit_or (bit_and v_4559 (notBool_ (eq (eq (extract v_4556 1 2) (expression.bv_nat 1 1)) (eq (extract v_4556 2 3) (expression.bv_nat 1 1))))) (bit_and (notBool_ v_4559) (bit_or (bit_and (notBool_ v_4568) undef) (bit_and v_4568 (eq v_4571 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (extract v_4556 0 1);
      pure ()
    pat_end;
    pattern fun (v_2515 : imm int) (v_2519 : reg (bv 64)) => do
      v_4582 <- getRegister cf;
      v_4585 <- getRegister v_2519;
      v_4590 <- eval (urem (concat (expression.bv_nat 57 0) (bv_and (handleImmediateWithSignExtend v_2515 8 8) (expression.bv_nat 8 63))) (expression.bv_nat 65 65));
      v_4592 <- eval (rorHelper (concat (mux (eq v_4582 (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0)) v_4585) (uvalueMInt v_4590) 0);
      v_4594 <- eval (extract v_4590 57 65);
      v_4595 <- eval (eq v_4594 (expression.bv_nat 8 1));
      v_4604 <- eval (eq v_4594 (expression.bv_nat 8 0));
      v_4607 <- getRegister of;
      setRegister (lhs.of_reg v_2519) (extract v_4592 1 65);
      setRegister of (mux (bit_or (bit_and v_4595 (notBool_ (eq (eq (extract v_4592 1 2) (expression.bv_nat 1 1)) (eq (extract v_4592 2 3) (expression.bv_nat 1 1))))) (bit_and (notBool_ v_4595) (bit_or (bit_and (notBool_ v_4604) undef) (bit_and v_4604 (eq v_4607 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (extract v_4592 0 1);
      pure ()
    pat_end;
    pattern fun $0x1 (v_2523 : reg (bv 64)) => do
      v_4618 <- getRegister cf;
      v_4621 <- getRegister v_2523;
      v_4622 <- eval (concat (mux (eq v_4618 (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0)) v_4621);
      v_4624 <- eval (bitwidthMInt v_4622);
      v_4625 <- eval (sub v_4624 1);
      v_4629 <- eval (add (lshr v_4622 1) (concat (extract v_4622 v_4625 v_4624) (mi v_4625 0)));
      setRegister (lhs.of_reg v_2523) (extract v_4629 1 65);
      setRegister of (mux (notBool_ (eq (eq (extract v_4629 1 2) (expression.bv_nat 1 1)) (eq (extract v_4629 2 3) (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (extract v_4629 0 1);
      pure ()
    pat_end;
    pattern fun cl (v_2501 : Mem) => do
      v_13927 <- evaluateAddress v_2501;
      v_13928 <- getRegister cf;
      v_13931 <- load v_13927 8;
      v_13933 <- getRegister rcx;
      v_13937 <- eval (urem (concat (expression.bv_nat 57 0) (bv_and (extract v_13933 56 64) (expression.bv_nat 8 63))) (expression.bv_nat 65 65));
      v_13939 <- eval (rorHelper (concat (mux (eq v_13928 (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0)) v_13931) (uvalueMInt v_13937) 0);
      store v_13927 (extract v_13939 1 65) 8;
      v_13943 <- eval (extract v_13937 57 65);
      v_13944 <- eval (eq v_13943 (expression.bv_nat 8 1));
      v_13953 <- eval (eq v_13943 (expression.bv_nat 8 0));
      v_13956 <- getRegister of;
      setRegister of (mux (bit_or (bit_and v_13944 (notBool_ (eq (eq (extract v_13939 1 2) (expression.bv_nat 1 1)) (eq (extract v_13939 2 3) (expression.bv_nat 1 1))))) (bit_and (notBool_ v_13944) (bit_or (bit_and (notBool_ v_13953) undef) (bit_and v_13953 (eq v_13956 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (extract v_13939 0 1);
      pure ()
    pat_end;
    pattern fun (v_2504 : imm int) (v_2505 : Mem) => do
      v_13965 <- evaluateAddress v_2505;
      v_13966 <- getRegister cf;
      v_13969 <- load v_13965 8;
      v_13974 <- eval (urem (concat (expression.bv_nat 57 0) (bv_and (handleImmediateWithSignExtend v_2504 8 8) (expression.bv_nat 8 63))) (expression.bv_nat 65 65));
      v_13976 <- eval (rorHelper (concat (mux (eq v_13966 (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0)) v_13969) (uvalueMInt v_13974) 0);
      store v_13965 (extract v_13976 1 65) 8;
      v_13980 <- eval (extract v_13974 57 65);
      v_13981 <- eval (eq v_13980 (expression.bv_nat 8 1));
      v_13990 <- eval (eq v_13980 (expression.bv_nat 8 0));
      v_13993 <- getRegister of;
      setRegister of (mux (bit_or (bit_and v_13981 (notBool_ (eq (eq (extract v_13976 1 2) (expression.bv_nat 1 1)) (eq (extract v_13976 2 3) (expression.bv_nat 1 1))))) (bit_and (notBool_ v_13981) (bit_or (bit_and (notBool_ v_13990) undef) (bit_and v_13990 (eq v_13993 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (extract v_13976 0 1);
      pure ()
    pat_end
