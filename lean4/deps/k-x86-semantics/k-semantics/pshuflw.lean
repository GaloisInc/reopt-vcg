def pshuflw1 : instruction :=
  definst "pshuflw" $ do
    pattern fun (v_2924 : imm int) (v_2922 : reg (bv 128)) (v_2923 : reg (bv 128)) => do
      v_7379 <- getRegister v_2922;
      v_7381 <- eval (handleImmediateWithSignExtend v_2924 8 8);
      v_7383 <- eval (concat (expression.bv_nat 126 0) (extract v_7381 0 2));
      v_7391 <- eval (concat (expression.bv_nat 126 0) (extract v_7381 2 4));
      v_7399 <- eval (concat (expression.bv_nat 126 0) (extract v_7381 4 6));
      v_7407 <- eval (concat (expression.bv_nat 126 0) (extract v_7381 6 8));
      setRegister (lhs.of_reg v_2923) (concat (extract v_7379 0 64) (concat (extract (lshr v_7379 (uvalueMInt (extract (shl v_7383 4) 0 (bitwidthMInt v_7383)))) 112 128) (concat (extract (lshr v_7379 (uvalueMInt (extract (shl v_7391 4) 0 (bitwidthMInt v_7391)))) 112 128) (concat (extract (lshr v_7379 (uvalueMInt (extract (shl v_7399 4) 0 (bitwidthMInt v_7399)))) 112 128) (extract (lshr v_7379 (uvalueMInt (extract (shl v_7407 4) 0 (bitwidthMInt v_7407)))) 112 128)))));
      pure ()
    pat_end;
    pattern fun (v_2918 : imm int) (v_2916 : Mem) (v_2917 : reg (bv 128)) => do
      v_14594 <- evaluateAddress v_2916;
      v_14595 <- load v_14594 16;
      v_14597 <- eval (handleImmediateWithSignExtend v_2918 8 8);
      v_14599 <- eval (concat (expression.bv_nat 126 0) (extract v_14597 0 2));
      v_14607 <- eval (concat (expression.bv_nat 126 0) (extract v_14597 2 4));
      v_14615 <- eval (concat (expression.bv_nat 126 0) (extract v_14597 4 6));
      v_14623 <- eval (concat (expression.bv_nat 126 0) (extract v_14597 6 8));
      setRegister (lhs.of_reg v_2917) (concat (extract v_14595 0 64) (concat (extract (lshr v_14595 (uvalueMInt (extract (shl v_14599 4) 0 (bitwidthMInt v_14599)))) 112 128) (concat (extract (lshr v_14595 (uvalueMInt (extract (shl v_14607 4) 0 (bitwidthMInt v_14607)))) 112 128) (concat (extract (lshr v_14595 (uvalueMInt (extract (shl v_14615 4) 0 (bitwidthMInt v_14615)))) 112 128) (extract (lshr v_14595 (uvalueMInt (extract (shl v_14623 4) 0 (bitwidthMInt v_14623)))) 112 128)))));
      pure ()
    pat_end
