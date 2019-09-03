def rcrl1 : instruction :=
  definst "rcrl" $ do
    pattern fun cl (v_2490 : reg (bv 32)) => do
      v_4438 <- getRegister cf;
      v_4441 <- getRegister v_2490;
      v_4443 <- getRegister rcx;
      v_4447 <- eval (urem (concat (expression.bv_nat 25 0) (bv_and (extract v_4443 56 64) (expression.bv_nat 8 31))) (expression.bv_nat 33 33));
      v_4449 <- eval (rorHelper (concat (mux (eq v_4438 (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0)) v_4441) (uvalueMInt v_4447) 0);
      v_4451 <- eval (extract v_4447 25 33);
      v_4452 <- eval (eq v_4451 (expression.bv_nat 8 1));
      v_4461 <- eval (eq v_4451 (expression.bv_nat 8 0));
      v_4464 <- getRegister of;
      setRegister (lhs.of_reg v_2490) (extract v_4449 1 33);
      setRegister of (mux (bit_or (bit_and v_4452 (notBool_ (eq (eq (extract v_4449 1 2) (expression.bv_nat 1 1)) (eq (extract v_4449 2 3) (expression.bv_nat 1 1))))) (bit_and (notBool_ v_4452) (bit_or (bit_and (notBool_ v_4461) undef) (bit_and v_4461 (eq v_4464 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (extract v_4449 0 1);
      pure ()
    pat_end;
    pattern fun (v_2492 : imm int) (v_2495 : reg (bv 32)) => do
      v_4475 <- getRegister cf;
      v_4478 <- getRegister v_2495;
      v_4483 <- eval (urem (concat (expression.bv_nat 25 0) (bv_and (handleImmediateWithSignExtend v_2492 8 8) (expression.bv_nat 8 31))) (expression.bv_nat 33 33));
      v_4485 <- eval (rorHelper (concat (mux (eq v_4475 (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0)) v_4478) (uvalueMInt v_4483) 0);
      v_4487 <- eval (extract v_4483 25 33);
      v_4488 <- eval (eq v_4487 (expression.bv_nat 8 1));
      v_4497 <- eval (eq v_4487 (expression.bv_nat 8 0));
      v_4500 <- getRegister of;
      setRegister (lhs.of_reg v_2495) (extract v_4485 1 33);
      setRegister of (mux (bit_or (bit_and v_4488 (notBool_ (eq (eq (extract v_4485 1 2) (expression.bv_nat 1 1)) (eq (extract v_4485 2 3) (expression.bv_nat 1 1))))) (bit_and (notBool_ v_4488) (bit_or (bit_and (notBool_ v_4497) undef) (bit_and v_4497 (eq v_4500 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (extract v_4485 0 1);
      pure ()
    pat_end;
    pattern fun $0x1 (v_2499 : reg (bv 32)) => do
      v_4511 <- getRegister cf;
      v_4514 <- getRegister v_2499;
      v_4515 <- eval (concat (mux (eq v_4511 (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0)) v_4514);
      v_4517 <- eval (bitwidthMInt v_4515);
      v_4518 <- eval (sub v_4517 1);
      v_4522 <- eval (add (lshr v_4515 1) (concat (extract v_4515 v_4518 v_4517) (mi v_4518 0)));
      setRegister (lhs.of_reg v_2499) (extract v_4522 1 33);
      setRegister of (mux (notBool_ (eq (eq (extract v_4522 1 2) (expression.bv_nat 1 1)) (eq (extract v_4522 2 3) (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (extract v_4522 0 1);
      pure ()
    pat_end;
    pattern fun cl (v_2478 : Mem) => do
      v_13802 <- evaluateAddress v_2478;
      v_13803 <- getRegister cf;
      v_13806 <- load v_13802 4;
      v_13808 <- getRegister rcx;
      v_13812 <- eval (urem (concat (expression.bv_nat 25 0) (bv_and (extract v_13808 56 64) (expression.bv_nat 8 31))) (expression.bv_nat 33 33));
      v_13814 <- eval (rorHelper (concat (mux (eq v_13803 (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0)) v_13806) (uvalueMInt v_13812) 0);
      store v_13802 (extract v_13814 1 33) 4;
      v_13818 <- eval (extract v_13812 25 33);
      v_13819 <- eval (eq v_13818 (expression.bv_nat 8 1));
      v_13828 <- eval (eq v_13818 (expression.bv_nat 8 0));
      v_13831 <- getRegister of;
      setRegister of (mux (bit_or (bit_and v_13819 (notBool_ (eq (eq (extract v_13814 1 2) (expression.bv_nat 1 1)) (eq (extract v_13814 2 3) (expression.bv_nat 1 1))))) (bit_and (notBool_ v_13819) (bit_or (bit_and (notBool_ v_13828) undef) (bit_and v_13828 (eq v_13831 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (extract v_13814 0 1);
      pure ()
    pat_end;
    pattern fun (v_2481 : imm int) (v_2482 : Mem) => do
      v_13840 <- evaluateAddress v_2482;
      v_13841 <- getRegister cf;
      v_13844 <- load v_13840 4;
      v_13849 <- eval (urem (concat (expression.bv_nat 25 0) (bv_and (handleImmediateWithSignExtend v_2481 8 8) (expression.bv_nat 8 31))) (expression.bv_nat 33 33));
      v_13851 <- eval (rorHelper (concat (mux (eq v_13841 (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0)) v_13844) (uvalueMInt v_13849) 0);
      store v_13840 (extract v_13851 1 33) 4;
      v_13855 <- eval (extract v_13849 25 33);
      v_13856 <- eval (eq v_13855 (expression.bv_nat 8 1));
      v_13865 <- eval (eq v_13855 (expression.bv_nat 8 0));
      v_13868 <- getRegister of;
      setRegister of (mux (bit_or (bit_and v_13856 (notBool_ (eq (eq (extract v_13851 1 2) (expression.bv_nat 1 1)) (eq (extract v_13851 2 3) (expression.bv_nat 1 1))))) (bit_and (notBool_ v_13856) (bit_or (bit_and (notBool_ v_13865) undef) (bit_and v_13865 (eq v_13868 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (extract v_13851 0 1);
      pure ()
    pat_end
