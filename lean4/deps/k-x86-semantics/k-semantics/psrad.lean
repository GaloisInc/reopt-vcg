def psrad1 : instruction :=
  definst "psrad" $ do
    pattern fun (v_3016 : imm int) (v_3017 : reg (bv 128)) => do
      v_7704 <- getRegister v_3017;
      v_7708 <- eval (handleImmediateWithSignExtend v_3016 8 8);
      v_7713 <- eval (uvalueMInt (mux (ugt (concat (expression.bv_nat 56 0) v_7708) (expression.bv_nat 64 31)) (expression.bv_nat 32 32) (concat (expression.bv_nat 24 0) v_7708)));
      setRegister (lhs.of_reg v_3017) (concat (ashr (mi 32 (svalueMInt (extract v_7704 0 32))) v_7713) (concat (ashr (mi 32 (svalueMInt (extract v_7704 32 64))) v_7713) (concat (ashr (mi 32 (svalueMInt (extract v_7704 64 96))) v_7713) (ashr (mi 32 (svalueMInt (extract v_7704 96 128))) v_7713))));
      pure ()
    pat_end;
    pattern fun (v_3025 : reg (bv 128)) (v_3026 : reg (bv 128)) => do
      v_7735 <- getRegister v_3026;
      v_7739 <- getRegister v_3025;
      v_7744 <- eval (uvalueMInt (mux (ugt (extract v_7739 64 128) (expression.bv_nat 64 31)) (expression.bv_nat 32 32) (extract v_7739 96 128)));
      setRegister (lhs.of_reg v_3026) (concat (ashr (mi 32 (svalueMInt (extract v_7735 0 32))) v_7744) (concat (ashr (mi 32 (svalueMInt (extract v_7735 32 64))) v_7744) (concat (ashr (mi 32 (svalueMInt (extract v_7735 64 96))) v_7744) (ashr (mi 32 (svalueMInt (extract v_7735 96 128))) v_7744))));
      pure ()
    pat_end;
    pattern fun (v_3021 : Mem) (v_3022 : reg (bv 128)) => do
      v_14488 <- getRegister v_3022;
      v_14492 <- evaluateAddress v_3021;
      v_14493 <- load v_14492 16;
      v_14498 <- eval (uvalueMInt (mux (ugt (extract v_14493 64 128) (expression.bv_nat 64 31)) (expression.bv_nat 32 32) (extract v_14493 96 128)));
      setRegister (lhs.of_reg v_3022) (concat (ashr (mi 32 (svalueMInt (extract v_14488 0 32))) v_14498) (concat (ashr (mi 32 (svalueMInt (extract v_14488 32 64))) v_14498) (concat (ashr (mi 32 (svalueMInt (extract v_14488 64 96))) v_14498) (ashr (mi 32 (svalueMInt (extract v_14488 96 128))) v_14498))));
      pure ()
    pat_end
