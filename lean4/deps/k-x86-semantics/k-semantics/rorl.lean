def rorl1 : instruction :=
  definst "rorl" $ do
    pattern fun cl (v_2703 : reg (bv 32)) => do
      v_5423 <- getRegister rcx;
      v_5425 <- eval (bv_and (extract v_5423 56 64) (expression.bv_nat 8 31));
      v_5426 <- eval (eq v_5425 (expression.bv_nat 8 0));
      v_5427 <- eval (notBool_ v_5426);
      v_5428 <- getRegister v_2703;
      v_5431 <- eval (rorHelper v_5428 (uvalueMInt (concat (expression.bv_nat 24 0) v_5425)) 0);
      v_5433 <- eval (eq (extract v_5431 0 1) (expression.bv_nat 1 1));
      v_5435 <- getRegister cf;
      v_5440 <- eval (eq v_5425 (expression.bv_nat 8 1));
      v_5448 <- getRegister of;
      setRegister (lhs.of_reg v_2703) v_5431;
      setRegister of (mux (bit_or (bit_and v_5440 (notBool_ (eq v_5433 (eq (extract v_5431 1 2) (expression.bv_nat 1 1))))) (bit_and (notBool_ v_5440) (bit_or (bit_and v_5427 undef) (bit_and v_5426 (eq v_5448 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux (bit_or (bit_and v_5427 v_5433) (bit_and v_5426 (eq v_5435 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2705 : imm int) (v_2708 : reg (bv 32)) => do
      v_5459 <- eval (bv_and (handleImmediateWithSignExtend v_2705 8 8) (expression.bv_nat 8 31));
      v_5460 <- eval (eq v_5459 (expression.bv_nat 8 0));
      v_5461 <- eval (notBool_ v_5460);
      v_5462 <- getRegister v_2708;
      v_5465 <- eval (rorHelper v_5462 (uvalueMInt (concat (expression.bv_nat 24 0) v_5459)) 0);
      v_5467 <- eval (eq (extract v_5465 0 1) (expression.bv_nat 1 1));
      v_5469 <- getRegister cf;
      v_5474 <- eval (eq v_5459 (expression.bv_nat 8 1));
      v_5482 <- getRegister of;
      setRegister (lhs.of_reg v_2708) v_5465;
      setRegister of (mux (bit_or (bit_and v_5474 (notBool_ (eq v_5467 (eq (extract v_5465 1 2) (expression.bv_nat 1 1))))) (bit_and (notBool_ v_5474) (bit_or (bit_and v_5461 undef) (bit_and v_5460 (eq v_5482 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux (bit_or (bit_and v_5461 v_5467) (bit_and v_5460 (eq v_5469 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun $0x1 (v_2712 : reg (bv 32)) => do
      v_5492 <- getRegister v_2712;
      v_5494 <- eval (bitwidthMInt v_5492);
      v_5495 <- eval (sub v_5494 1);
      v_5499 <- eval (add (lshr v_5492 1) (concat (extract v_5492 v_5495 v_5494) (mi v_5495 0)));
      v_5500 <- eval (extract v_5499 0 1);
      setRegister (lhs.of_reg v_2712) v_5499;
      setRegister of (mux (notBool_ (eq (eq v_5500 (expression.bv_nat 1 1)) (eq (extract v_5499 1 2) (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf v_5500;
      pure ()
    pat_end;
    pattern fun cl (v_2691 : Mem) => do
      v_14936 <- evaluateAddress v_2691;
      v_14937 <- load v_14936 4;
      v_14938 <- getRegister rcx;
      v_14940 <- eval (bv_and (extract v_14938 56 64) (expression.bv_nat 8 31));
      v_14943 <- eval (rorHelper v_14937 (uvalueMInt (concat (expression.bv_nat 24 0) v_14940)) 0);
      store v_14936 v_14943 4;
      v_14945 <- eval (eq v_14940 (expression.bv_nat 8 0));
      v_14946 <- eval (notBool_ v_14945);
      v_14948 <- eval (eq (extract v_14943 0 1) (expression.bv_nat 1 1));
      v_14950 <- getRegister cf;
      v_14955 <- eval (eq v_14940 (expression.bv_nat 8 1));
      v_14963 <- getRegister of;
      setRegister of (mux (bit_or (bit_and v_14955 (notBool_ (eq v_14948 (eq (extract v_14943 1 2) (expression.bv_nat 1 1))))) (bit_and (notBool_ v_14955) (bit_or (bit_and v_14946 undef) (bit_and v_14945 (eq v_14963 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux (bit_or (bit_and v_14946 v_14948) (bit_and v_14945 (eq v_14950 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2694 : imm int) (v_2695 : Mem) => do
      v_14972 <- evaluateAddress v_2695;
      v_14973 <- load v_14972 4;
      v_14975 <- eval (bv_and (handleImmediateWithSignExtend v_2694 8 8) (expression.bv_nat 8 31));
      v_14978 <- eval (rorHelper v_14973 (uvalueMInt (concat (expression.bv_nat 24 0) v_14975)) 0);
      store v_14972 v_14978 4;
      v_14980 <- eval (eq v_14975 (expression.bv_nat 8 0));
      v_14981 <- eval (notBool_ v_14980);
      v_14983 <- eval (eq (extract v_14978 0 1) (expression.bv_nat 1 1));
      v_14985 <- getRegister cf;
      v_14990 <- eval (eq v_14975 (expression.bv_nat 8 1));
      v_14998 <- getRegister of;
      setRegister of (mux (bit_or (bit_and v_14990 (notBool_ (eq v_14983 (eq (extract v_14978 1 2) (expression.bv_nat 1 1))))) (bit_and (notBool_ v_14990) (bit_or (bit_and v_14981 undef) (bit_and v_14980 (eq v_14998 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux (bit_or (bit_and v_14981 v_14983) (bit_and v_14980 (eq v_14985 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end
