def rorw1 : instruction :=
  definst "rorw" $ do
    pattern fun cl (v_2761 : reg (bv 16)) => do
      v_5640 <- getRegister rcx;
      v_5642 <- eval (bv_and (extract v_5640 56 64) (expression.bv_nat 8 31));
      v_5643 <- eval (eq v_5642 (expression.bv_nat 8 0));
      v_5644 <- eval (notBool_ v_5643);
      v_5645 <- getRegister v_2761;
      v_5648 <- eval (rorHelper v_5645 (uvalueMInt (concat (expression.bv_nat 8 0) v_5642)) 0);
      v_5650 <- eval (eq (extract v_5648 0 1) (expression.bv_nat 1 1));
      v_5652 <- getRegister cf;
      v_5657 <- eval (eq v_5642 (expression.bv_nat 8 1));
      v_5665 <- getRegister of;
      setRegister (lhs.of_reg v_2761) v_5648;
      setRegister of (mux (bit_or (bit_and v_5657 (notBool_ (eq v_5650 (eq (extract v_5648 1 2) (expression.bv_nat 1 1))))) (bit_and (notBool_ v_5657) (bit_or (bit_and v_5644 undef) (bit_and v_5643 (eq v_5665 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux (bit_or (bit_and v_5644 v_5650) (bit_and v_5643 (eq v_5652 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2764 : imm int) (v_2766 : reg (bv 16)) => do
      v_5676 <- eval (bv_and (handleImmediateWithSignExtend v_2764 8 8) (expression.bv_nat 8 31));
      v_5677 <- eval (eq v_5676 (expression.bv_nat 8 0));
      v_5678 <- eval (notBool_ v_5677);
      v_5679 <- getRegister v_2766;
      v_5682 <- eval (rorHelper v_5679 (uvalueMInt (concat (expression.bv_nat 8 0) v_5676)) 0);
      v_5684 <- eval (eq (extract v_5682 0 1) (expression.bv_nat 1 1));
      v_5686 <- getRegister cf;
      v_5691 <- eval (eq v_5676 (expression.bv_nat 8 1));
      v_5699 <- getRegister of;
      setRegister (lhs.of_reg v_2766) v_5682;
      setRegister of (mux (bit_or (bit_and v_5691 (notBool_ (eq v_5684 (eq (extract v_5682 1 2) (expression.bv_nat 1 1))))) (bit_and (notBool_ v_5691) (bit_or (bit_and v_5678 undef) (bit_and v_5677 (eq v_5699 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux (bit_or (bit_and v_5678 v_5684) (bit_and v_5677 (eq v_5686 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun $0x1 (v_2770 : reg (bv 16)) => do
      v_5709 <- getRegister v_2770;
      v_5713 <- eval (add (lshr v_5709 1) (concat (extract v_5709 15 16) (expression.bv_nat 15 0)));
      v_5714 <- eval (extract v_5713 0 1);
      setRegister (lhs.of_reg v_2770) v_5713;
      setRegister of (mux (notBool_ (eq (eq v_5714 (expression.bv_nat 1 1)) (eq (extract v_5713 1 2) (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf v_5714;
      pure ()
    pat_end;
    pattern fun cl (v_2750 : Mem) => do
      v_15064 <- evaluateAddress v_2750;
      v_15065 <- load v_15064 2;
      v_15066 <- getRegister rcx;
      v_15068 <- eval (bv_and (extract v_15066 56 64) (expression.bv_nat 8 31));
      v_15071 <- eval (rorHelper v_15065 (uvalueMInt (concat (expression.bv_nat 8 0) v_15068)) 0);
      store v_15064 v_15071 2;
      v_15073 <- eval (eq v_15068 (expression.bv_nat 8 0));
      v_15074 <- eval (notBool_ v_15073);
      v_15076 <- eval (eq (extract v_15071 0 1) (expression.bv_nat 1 1));
      v_15078 <- getRegister cf;
      v_15083 <- eval (eq v_15068 (expression.bv_nat 8 1));
      v_15091 <- getRegister of;
      setRegister of (mux (bit_or (bit_and v_15083 (notBool_ (eq v_15076 (eq (extract v_15071 1 2) (expression.bv_nat 1 1))))) (bit_and (notBool_ v_15083) (bit_or (bit_and v_15074 undef) (bit_and v_15073 (eq v_15091 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux (bit_or (bit_and v_15074 v_15076) (bit_and v_15073 (eq v_15078 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2754 : imm int) (v_2753 : Mem) => do
      v_15100 <- evaluateAddress v_2753;
      v_15101 <- load v_15100 2;
      v_15103 <- eval (bv_and (handleImmediateWithSignExtend v_2754 8 8) (expression.bv_nat 8 31));
      v_15106 <- eval (rorHelper v_15101 (uvalueMInt (concat (expression.bv_nat 8 0) v_15103)) 0);
      store v_15100 v_15106 2;
      v_15108 <- eval (eq v_15103 (expression.bv_nat 8 0));
      v_15109 <- eval (notBool_ v_15108);
      v_15111 <- eval (eq (extract v_15106 0 1) (expression.bv_nat 1 1));
      v_15113 <- getRegister cf;
      v_15118 <- eval (eq v_15103 (expression.bv_nat 8 1));
      v_15126 <- getRegister of;
      setRegister of (mux (bit_or (bit_and v_15118 (notBool_ (eq v_15111 (eq (extract v_15106 1 2) (expression.bv_nat 1 1))))) (bit_and (notBool_ v_15118) (bit_or (bit_and v_15109 undef) (bit_and v_15108 (eq v_15126 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux (bit_or (bit_and v_15109 v_15111) (bit_and v_15108 (eq v_15113 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end
