def sarb1 : instruction :=
  definst "sarb" $ do
    pattern fun cl (v_3012 : reg (bv 8)) => do
      v_7061 <- getRegister rcx;
      v_7063 <- eval (bv_and (extract v_7061 56 64) (expression.bv_nat 8 31));
      v_7064 <- eval (eq v_7063 (expression.bv_nat 8 0));
      v_7065 <- eval (notBool_ v_7064);
      v_7066 <- getRegister v_3012;
      v_7067 <- eval (concat v_7066 (expression.bv_nat 1 0));
      v_7073 <- eval (ashr (mi (bitwidthMInt v_7067) (svalueMInt v_7067)) (uvalueMInt (concat (expression.bv_nat 1 0) v_7063)));
      v_7077 <- getRegister cf;
      v_7083 <- eval (eq (extract v_7073 0 1) (expression.bv_nat 1 1));
      v_7085 <- getRegister sf;
      v_7090 <- eval (bit_and v_7065 undef);
      v_7091 <- getRegister af;
      v_7096 <- eval (extract v_7073 0 8);
      v_7099 <- getRegister zf;
      v_7132 <- getRegister pf;
      v_7139 <- getRegister of;
      setRegister (lhs.of_reg v_3012) v_7096;
      setRegister of (mux (bit_and (notBool_ (eq v_7063 (expression.bv_nat 8 1))) (bit_or v_7090 (bit_and v_7064 (eq v_7139 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (mux (bit_or (bit_and v_7065 (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (extract v_7073 7 8) (expression.bv_nat 1 1)) (eq (extract v_7073 6 7) (expression.bv_nat 1 1)))) (eq (extract v_7073 5 6) (expression.bv_nat 1 1)))) (eq (extract v_7073 4 5) (expression.bv_nat 1 1)))) (eq (extract v_7073 3 4) (expression.bv_nat 1 1)))) (eq (extract v_7073 2 3) (expression.bv_nat 1 1)))) (eq (extract v_7073 1 2) (expression.bv_nat 1 1)))) v_7083)) (bit_and v_7064 (eq v_7132 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (mux (bit_or (bit_and v_7065 (eq v_7096 (expression.bv_nat 8 0))) (bit_and v_7064 (eq v_7099 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af (mux (bit_or v_7090 (bit_and v_7064 (eq v_7091 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (mux (bit_or (bit_and v_7065 v_7083) (bit_and v_7064 (eq v_7085 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux (bit_or (bit_and v_7065 (eq (extract v_7073 8 9) (expression.bv_nat 1 1))) (bit_and v_7064 (eq v_7077 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_3013 : imm int) (v_3017 : reg (bv 8)) => do
      v_7153 <- eval (bv_and (handleImmediateWithSignExtend v_3013 8 8) (expression.bv_nat 8 31));
      v_7154 <- eval (eq v_7153 (expression.bv_nat 8 0));
      v_7155 <- eval (notBool_ v_7154);
      v_7156 <- getRegister v_3017;
      v_7157 <- eval (concat v_7156 (expression.bv_nat 1 0));
      v_7163 <- eval (ashr (mi (bitwidthMInt v_7157) (svalueMInt v_7157)) (uvalueMInt (concat (expression.bv_nat 1 0) v_7153)));
      v_7167 <- getRegister cf;
      v_7173 <- eval (eq (extract v_7163 0 1) (expression.bv_nat 1 1));
      v_7175 <- getRegister sf;
      v_7180 <- eval (bit_and v_7155 undef);
      v_7181 <- getRegister af;
      v_7186 <- eval (extract v_7163 0 8);
      v_7189 <- getRegister zf;
      v_7222 <- getRegister pf;
      v_7229 <- getRegister of;
      setRegister (lhs.of_reg v_3017) v_7186;
      setRegister of (mux (bit_and (notBool_ (eq v_7153 (expression.bv_nat 8 1))) (bit_or v_7180 (bit_and v_7154 (eq v_7229 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (mux (bit_or (bit_and v_7155 (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (extract v_7163 7 8) (expression.bv_nat 1 1)) (eq (extract v_7163 6 7) (expression.bv_nat 1 1)))) (eq (extract v_7163 5 6) (expression.bv_nat 1 1)))) (eq (extract v_7163 4 5) (expression.bv_nat 1 1)))) (eq (extract v_7163 3 4) (expression.bv_nat 1 1)))) (eq (extract v_7163 2 3) (expression.bv_nat 1 1)))) (eq (extract v_7163 1 2) (expression.bv_nat 1 1)))) v_7173)) (bit_and v_7154 (eq v_7222 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (mux (bit_or (bit_and v_7155 (eq v_7186 (expression.bv_nat 8 0))) (bit_and v_7154 (eq v_7189 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af (mux (bit_or v_7180 (bit_and v_7154 (eq v_7181 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (mux (bit_or (bit_and v_7155 v_7173) (bit_and v_7154 (eq v_7175 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux (bit_or (bit_and v_7155 (eq (extract v_7163 8 9) (expression.bv_nat 1 1))) (bit_and v_7154 (eq v_7167 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun $0x1 (v_3024 : reg (bv 8)) => do
      v_7244 <- getRegister v_3024;
      v_7245 <- eval (concat v_7244 (expression.bv_nat 1 0));
      v_7249 <- eval (ashr (mi (bitwidthMInt v_7245) (svalueMInt v_7245)) 1);
      v_7252 <- eval (extract v_7249 0 8);
      setRegister (lhs.of_reg v_3024) v_7252;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (parityFlag v_7252);
      setRegister zf (zeroFlag v_7252);
      setRegister af undef;
      setRegister sf (extract v_7249 0 1);
      setRegister cf (extract v_7249 8 9);
      pure ()
    pat_end;
    pattern fun (v_3020 : reg (bv 8)) => do
      v_9746 <- getRegister v_3020;
      v_9747 <- eval (concat v_9746 (expression.bv_nat 1 0));
      v_9751 <- eval (ashr (mi (bitwidthMInt v_9747) (svalueMInt v_9747)) 1);
      v_9758 <- eval (extract v_9751 0 8);
      setRegister (lhs.of_reg v_3020) v_9758;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (parityFlag v_9758);
      setRegister zf (zeroFlag v_9758);
      setRegister af (mux undef (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (mux (eq (extract v_9751 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux (eq (extract v_9751 8 9) (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_3020 : reg (bv 8)) => do
      v_9768 <- getRegister v_3020;
      v_9769 <- eval (concat v_9768 (expression.bv_nat 1 0));
      v_9773 <- eval (ashr (mi (bitwidthMInt v_9769) (svalueMInt v_9769)) 1);
      v_9776 <- eval (extract v_9773 0 8);
      setRegister (lhs.of_reg v_3020) v_9776;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (parityFlag v_9776);
      setRegister zf (zeroFlag v_9776);
      setRegister af undef;
      setRegister sf (extract v_9773 0 1);
      setRegister cf (extract v_9773 8 9);
      pure ()
    pat_end;
    pattern fun (v_3036 : reg (bv 8)) => do
      v_9786 <- getRegister v_3036;
      v_9787 <- eval (concat v_9786 (expression.bv_nat 1 0));
      v_9791 <- eval (ashr (mi (bitwidthMInt v_9787) (svalueMInt v_9787)) 1);
      v_9798 <- eval (extract v_9791 0 8);
      setRegister (lhs.of_reg v_3036) v_9798;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (parityFlag v_9798);
      setRegister af (mux undef (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (zeroFlag v_9798);
      setRegister sf (mux (eq (extract v_9791 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux (eq (extract v_9791 8 9) (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_3036 : reg (bv 8)) => do
      v_9808 <- getRegister v_3036;
      v_9809 <- eval (concat v_9808 (expression.bv_nat 1 0));
      v_9813 <- eval (ashr (mi (bitwidthMInt v_9809) (svalueMInt v_9809)) 1);
      v_9816 <- eval (extract v_9813 0 8);
      setRegister (lhs.of_reg v_3036) v_9816;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (parityFlag v_9816);
      setRegister af undef;
      setRegister zf (zeroFlag v_9816);
      setRegister sf (extract v_9813 0 1);
      setRegister cf (extract v_9813 8 9);
      pure ()
    pat_end;
    pattern fun cl (v_2996 : Mem) => do
      v_16623 <- evaluateAddress v_2996;
      v_16624 <- load v_16623 1;
      v_16625 <- eval (concat v_16624 (expression.bv_nat 1 0));
      v_16629 <- getRegister rcx;
      v_16631 <- eval (bv_and (extract v_16629 56 64) (expression.bv_nat 8 31));
      v_16634 <- eval (ashr (mi (bitwidthMInt v_16625) (svalueMInt v_16625)) (uvalueMInt (concat (expression.bv_nat 1 0) v_16631)));
      v_16635 <- eval (extract v_16634 0 8);
      store v_16623 v_16635 1;
      v_16637 <- eval (eq v_16631 (expression.bv_nat 8 0));
      v_16638 <- eval (notBool_ v_16637);
      v_16642 <- getRegister cf;
      v_16648 <- eval (eq (extract v_16634 0 1) (expression.bv_nat 1 1));
      v_16650 <- getRegister sf;
      v_16657 <- getRegister zf;
      v_16662 <- eval (bit_and v_16638 undef);
      v_16663 <- getRegister af;
      v_16696 <- getRegister pf;
      v_16703 <- getRegister of;
      setRegister of (mux (bit_and (notBool_ (eq v_16631 (expression.bv_nat 8 1))) (bit_or v_16662 (bit_and v_16637 (eq v_16703 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (mux (bit_or (bit_and v_16638 (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (extract v_16634 7 8) (expression.bv_nat 1 1)) (eq (extract v_16634 6 7) (expression.bv_nat 1 1)))) (eq (extract v_16634 5 6) (expression.bv_nat 1 1)))) (eq (extract v_16634 4 5) (expression.bv_nat 1 1)))) (eq (extract v_16634 3 4) (expression.bv_nat 1 1)))) (eq (extract v_16634 2 3) (expression.bv_nat 1 1)))) (eq (extract v_16634 1 2) (expression.bv_nat 1 1)))) v_16648)) (bit_and v_16637 (eq v_16696 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af (mux (bit_or v_16662 (bit_and v_16637 (eq v_16663 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (mux (bit_or (bit_and v_16638 (eq v_16635 (expression.bv_nat 8 0))) (bit_and v_16637 (eq v_16657 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (mux (bit_or (bit_and v_16638 v_16648) (bit_and v_16637 (eq v_16650 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux (bit_or (bit_and v_16638 (eq (extract v_16634 8 9) (expression.bv_nat 1 1))) (bit_and v_16637 (eq v_16642 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2999 : imm int) (v_3000 : Mem) => do
      v_16715 <- evaluateAddress v_3000;
      v_16716 <- load v_16715 1;
      v_16717 <- eval (concat v_16716 (expression.bv_nat 1 0));
      v_16722 <- eval (bv_and (handleImmediateWithSignExtend v_2999 8 8) (expression.bv_nat 8 31));
      v_16725 <- eval (ashr (mi (bitwidthMInt v_16717) (svalueMInt v_16717)) (uvalueMInt (concat (expression.bv_nat 1 0) v_16722)));
      v_16726 <- eval (extract v_16725 0 8);
      store v_16715 v_16726 1;
      v_16728 <- eval (eq v_16722 (expression.bv_nat 8 0));
      v_16729 <- eval (notBool_ v_16728);
      v_16733 <- getRegister cf;
      v_16739 <- eval (eq (extract v_16725 0 1) (expression.bv_nat 1 1));
      v_16741 <- getRegister sf;
      v_16748 <- getRegister zf;
      v_16753 <- eval (bit_and v_16729 undef);
      v_16754 <- getRegister af;
      v_16787 <- getRegister pf;
      v_16794 <- getRegister of;
      setRegister of (mux (bit_and (notBool_ (eq v_16722 (expression.bv_nat 8 1))) (bit_or v_16753 (bit_and v_16728 (eq v_16794 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (mux (bit_or (bit_and v_16729 (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (extract v_16725 7 8) (expression.bv_nat 1 1)) (eq (extract v_16725 6 7) (expression.bv_nat 1 1)))) (eq (extract v_16725 5 6) (expression.bv_nat 1 1)))) (eq (extract v_16725 4 5) (expression.bv_nat 1 1)))) (eq (extract v_16725 3 4) (expression.bv_nat 1 1)))) (eq (extract v_16725 2 3) (expression.bv_nat 1 1)))) (eq (extract v_16725 1 2) (expression.bv_nat 1 1)))) v_16739)) (bit_and v_16728 (eq v_16787 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af (mux (bit_or v_16753 (bit_and v_16728 (eq v_16754 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (mux (bit_or (bit_and v_16729 (eq v_16726 (expression.bv_nat 8 0))) (bit_and v_16728 (eq v_16748 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (mux (bit_or (bit_and v_16729 v_16739) (bit_and v_16728 (eq v_16741 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux (bit_or (bit_and v_16729 (eq (extract v_16725 8 9) (expression.bv_nat 1 1))) (bit_and v_16728 (eq v_16733 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_3005 : Mem) => do
      v_18396 <- evaluateAddress v_3005;
      v_18397 <- load v_18396 1;
      v_18398 <- eval (concat v_18397 (expression.bv_nat 1 0));
      v_18402 <- eval (ashr (mi (bitwidthMInt v_18398) (svalueMInt v_18398)) 1);
      v_18403 <- eval (extract v_18402 0 8);
      store v_18396 v_18403 1;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (parityFlag v_18403);
      setRegister af (mux undef (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (zeroFlag v_18403);
      setRegister sf (mux (eq (extract v_18402 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux (eq (extract v_18402 8 9) (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_3005 : Mem) => do
      v_18419 <- evaluateAddress v_3005;
      v_18420 <- load v_18419 1;
      v_18421 <- eval (concat v_18420 (expression.bv_nat 1 0));
      v_18425 <- eval (ashr (mi (bitwidthMInt v_18421) (svalueMInt v_18421)) 1);
      v_18426 <- eval (extract v_18425 0 8);
      store v_18419 v_18426 1;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (parityFlag v_18426);
      setRegister af undef;
      setRegister zf (zeroFlag v_18426);
      setRegister sf (extract v_18425 0 1);
      setRegister cf (extract v_18425 8 9);
      pure ()
    pat_end
