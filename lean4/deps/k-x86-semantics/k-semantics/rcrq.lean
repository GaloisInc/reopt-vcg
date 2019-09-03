def rcrq1 : instruction :=
  definst "rcrq" $ do
    pattern fun cl (v_2525 : reg (bv 64)) => do
      v_4593 <- getRegister cf;
      v_4596 <- getRegister v_2525;
      v_4598 <- getRegister rcx;
      v_4602 <- eval (urem (concat (expression.bv_nat 57 0) (bv_and (extract v_4598 56 64) (expression.bv_nat 8 63))) (expression.bv_nat 65 65));
      v_4604 <- eval (rorHelper (concat (mux (eq v_4593 (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0)) v_4596) (uvalueMInt v_4602) 0);
      v_4606 <- eval (extract v_4602 57 65);
      v_4607 <- eval (eq v_4606 (expression.bv_nat 8 1));
      v_4616 <- eval (eq v_4606 (expression.bv_nat 8 0));
      v_4619 <- getRegister of;
      setRegister (lhs.of_reg v_2525) (extract v_4604 1 65);
      setRegister of (mux (bit_or (bit_and v_4607 (notBool_ (eq (eq (extract v_4604 1 2) (expression.bv_nat 1 1)) (eq (extract v_4604 2 3) (expression.bv_nat 1 1))))) (bit_and (notBool_ v_4607) (bit_or (bit_and (notBool_ v_4616) undef) (bit_and v_4616 (eq v_4619 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (extract v_4604 0 1);
      pure ()
    pat_end;
    pattern fun (v_2528 : imm int) (v_2530 : reg (bv 64)) => do
      v_4630 <- getRegister cf;
      v_4633 <- getRegister v_2530;
      v_4638 <- eval (urem (concat (expression.bv_nat 57 0) (bv_and (handleImmediateWithSignExtend v_2528 8 8) (expression.bv_nat 8 63))) (expression.bv_nat 65 65));
      v_4640 <- eval (rorHelper (concat (mux (eq v_4630 (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0)) v_4633) (uvalueMInt v_4638) 0);
      v_4642 <- eval (extract v_4638 57 65);
      v_4643 <- eval (eq v_4642 (expression.bv_nat 8 1));
      v_4652 <- eval (eq v_4642 (expression.bv_nat 8 0));
      v_4655 <- getRegister of;
      setRegister (lhs.of_reg v_2530) (extract v_4640 1 65);
      setRegister of (mux (bit_or (bit_and v_4643 (notBool_ (eq (eq (extract v_4640 1 2) (expression.bv_nat 1 1)) (eq (extract v_4640 2 3) (expression.bv_nat 1 1))))) (bit_and (notBool_ v_4643) (bit_or (bit_and (notBool_ v_4652) undef) (bit_and v_4652 (eq v_4655 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (extract v_4640 0 1);
      pure ()
    pat_end;
    pattern fun $0x1 (v_2534 : reg (bv 64)) => do
      v_4666 <- getRegister cf;
      v_4668 <- eval (mux (eq v_4666 (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      v_4669 <- getRegister v_2534;
      v_4670 <- eval (concat v_4668 v_4669);
      v_4673 <- eval (add (bitwidthMInt v_4668) 64);
      v_4674 <- eval (sub v_4673 1);
      v_4678 <- eval (add (lshr v_4670 1) (concat (extract v_4670 v_4674 v_4673) (mi v_4674 0)));
      setRegister (lhs.of_reg v_2534) (extract v_4678 1 65);
      setRegister of (mux (notBool_ (eq (eq (extract v_4678 1 2) (expression.bv_nat 1 1)) (eq (extract v_4678 2 3) (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (extract v_4678 0 1);
      pure ()
    pat_end;
    pattern fun cl (v_2514 : Mem) => do
      v_13837 <- evaluateAddress v_2514;
      v_13838 <- getRegister cf;
      v_13841 <- load v_13837 8;
      v_13843 <- getRegister rcx;
      v_13847 <- eval (urem (concat (expression.bv_nat 57 0) (bv_and (extract v_13843 56 64) (expression.bv_nat 8 63))) (expression.bv_nat 65 65));
      v_13849 <- eval (rorHelper (concat (mux (eq v_13838 (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0)) v_13841) (uvalueMInt v_13847) 0);
      store v_13837 (extract v_13849 1 65) 8;
      v_13853 <- eval (extract v_13847 57 65);
      v_13854 <- eval (eq v_13853 (expression.bv_nat 8 1));
      v_13863 <- eval (eq v_13853 (expression.bv_nat 8 0));
      v_13866 <- getRegister of;
      setRegister of (mux (bit_or (bit_and v_13854 (notBool_ (eq (eq (extract v_13849 1 2) (expression.bv_nat 1 1)) (eq (extract v_13849 2 3) (expression.bv_nat 1 1))))) (bit_and (notBool_ v_13854) (bit_or (bit_and (notBool_ v_13863) undef) (bit_and v_13863 (eq v_13866 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (extract v_13849 0 1);
      pure ()
    pat_end;
    pattern fun (v_2518 : imm int) (v_2517 : Mem) => do
      v_13875 <- evaluateAddress v_2517;
      v_13876 <- getRegister cf;
      v_13879 <- load v_13875 8;
      v_13884 <- eval (urem (concat (expression.bv_nat 57 0) (bv_and (handleImmediateWithSignExtend v_2518 8 8) (expression.bv_nat 8 63))) (expression.bv_nat 65 65));
      v_13886 <- eval (rorHelper (concat (mux (eq v_13876 (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0)) v_13879) (uvalueMInt v_13884) 0);
      store v_13875 (extract v_13886 1 65) 8;
      v_13890 <- eval (extract v_13884 57 65);
      v_13891 <- eval (eq v_13890 (expression.bv_nat 8 1));
      v_13900 <- eval (eq v_13890 (expression.bv_nat 8 0));
      v_13903 <- getRegister of;
      setRegister of (mux (bit_or (bit_and v_13891 (notBool_ (eq (eq (extract v_13886 1 2) (expression.bv_nat 1 1)) (eq (extract v_13886 2 3) (expression.bv_nat 1 1))))) (bit_and (notBool_ v_13891) (bit_or (bit_and (notBool_ v_13900) undef) (bit_and v_13900 (eq v_13903 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (extract v_13886 0 1);
      pure ()
    pat_end
