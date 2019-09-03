def rorq1 : instruction :=
  definst "rorq" $ do
    pattern fun cl (v_2738 : reg (bv 64)) => do
      v_5546 <- getRegister rcx;
      v_5548 <- eval (bv_and (extract v_5546 56 64) (expression.bv_nat 8 63));
      v_5549 <- eval (eq v_5548 (expression.bv_nat 8 0));
      v_5550 <- eval (notBool_ v_5549);
      v_5551 <- getRegister v_2738;
      v_5554 <- eval (rorHelper v_5551 (uvalueMInt (concat (expression.bv_nat 56 0) v_5548)) 0);
      v_5556 <- eval (eq (extract v_5554 0 1) (expression.bv_nat 1 1));
      v_5558 <- getRegister cf;
      v_5563 <- eval (eq v_5548 (expression.bv_nat 8 1));
      v_5571 <- getRegister of;
      setRegister (lhs.of_reg v_2738) v_5554;
      setRegister of (mux (bit_or (bit_and v_5563 (notBool_ (eq v_5556 (eq (extract v_5554 1 2) (expression.bv_nat 1 1))))) (bit_and (notBool_ v_5563) (bit_or (bit_and v_5550 undef) (bit_and v_5549 (eq v_5571 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux (bit_or (bit_and v_5550 v_5556) (bit_and v_5549 (eq v_5558 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2741 : imm int) (v_2743 : reg (bv 64)) => do
      v_5582 <- eval (bv_and (handleImmediateWithSignExtend v_2741 8 8) (expression.bv_nat 8 63));
      v_5583 <- eval (eq v_5582 (expression.bv_nat 8 0));
      v_5584 <- eval (notBool_ v_5583);
      v_5585 <- getRegister v_2743;
      v_5588 <- eval (rorHelper v_5585 (uvalueMInt (concat (expression.bv_nat 56 0) v_5582)) 0);
      v_5590 <- eval (eq (extract v_5588 0 1) (expression.bv_nat 1 1));
      v_5592 <- getRegister cf;
      v_5597 <- eval (eq v_5582 (expression.bv_nat 8 1));
      v_5605 <- getRegister of;
      setRegister (lhs.of_reg v_2743) v_5588;
      setRegister of (mux (bit_or (bit_and v_5597 (notBool_ (eq v_5590 (eq (extract v_5588 1 2) (expression.bv_nat 1 1))))) (bit_and (notBool_ v_5597) (bit_or (bit_and v_5584 undef) (bit_and v_5583 (eq v_5605 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux (bit_or (bit_and v_5584 v_5590) (bit_and v_5583 (eq v_5592 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun $0x1 (v_2747 : reg (bv 64)) => do
      v_5615 <- getRegister v_2747;
      v_5619 <- eval (add (lshr v_5615 1) (concat (extract v_5615 63 64) (expression.bv_nat 63 0)));
      v_5620 <- eval (extract v_5619 0 1);
      setRegister (lhs.of_reg v_2747) v_5619;
      setRegister of (mux (notBool_ (eq (eq v_5620 (expression.bv_nat 1 1)) (eq (extract v_5619 1 2) (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf v_5620;
      pure ()
    pat_end;
    pattern fun cl (v_2727 : Mem) => do
      v_14927 <- evaluateAddress v_2727;
      v_14928 <- load v_14927 8;
      v_14929 <- getRegister rcx;
      v_14931 <- eval (bv_and (extract v_14929 56 64) (expression.bv_nat 8 63));
      v_14934 <- eval (rorHelper v_14928 (uvalueMInt (concat (expression.bv_nat 56 0) v_14931)) 0);
      store v_14927 v_14934 8;
      v_14936 <- eval (eq v_14931 (expression.bv_nat 8 0));
      v_14937 <- eval (notBool_ v_14936);
      v_14939 <- eval (eq (extract v_14934 0 1) (expression.bv_nat 1 1));
      v_14941 <- getRegister cf;
      v_14946 <- eval (eq v_14931 (expression.bv_nat 8 1));
      v_14954 <- getRegister of;
      setRegister of (mux (bit_or (bit_and v_14946 (notBool_ (eq v_14939 (eq (extract v_14934 1 2) (expression.bv_nat 1 1))))) (bit_and (notBool_ v_14946) (bit_or (bit_and v_14937 undef) (bit_and v_14936 (eq v_14954 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux (bit_or (bit_and v_14937 v_14939) (bit_and v_14936 (eq v_14941 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2731 : imm int) (v_2730 : Mem) => do
      v_14963 <- evaluateAddress v_2730;
      v_14964 <- load v_14963 8;
      v_14966 <- eval (bv_and (handleImmediateWithSignExtend v_2731 8 8) (expression.bv_nat 8 63));
      v_14969 <- eval (rorHelper v_14964 (uvalueMInt (concat (expression.bv_nat 56 0) v_14966)) 0);
      store v_14963 v_14969 8;
      v_14971 <- eval (eq v_14966 (expression.bv_nat 8 0));
      v_14972 <- eval (notBool_ v_14971);
      v_14974 <- eval (eq (extract v_14969 0 1) (expression.bv_nat 1 1));
      v_14976 <- getRegister cf;
      v_14981 <- eval (eq v_14966 (expression.bv_nat 8 1));
      v_14989 <- getRegister of;
      setRegister of (mux (bit_or (bit_and v_14981 (notBool_ (eq v_14974 (eq (extract v_14969 1 2) (expression.bv_nat 1 1))))) (bit_and (notBool_ v_14981) (bit_or (bit_and v_14972 undef) (bit_and v_14971 (eq v_14989 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux (bit_or (bit_and v_14972 v_14974) (bit_and v_14971 (eq v_14976 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end
