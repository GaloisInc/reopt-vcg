def palignr1 : instruction :=
  definst "palignr" $ do
    pattern fun (v_3183 : imm int) (v_3185 : reg (bv 128)) (v_3186 : reg (bv 128)) => do
      v_6395 <- getRegister v_3186;
      v_6396 <- getRegister v_3185;
      v_6399 <- eval (concat (expression.bv_nat 248 0) (handleImmediateWithSignExtend v_3183 8 8));
      setRegister (lhs.of_reg v_3186) (extract (lshr (concat v_6395 v_6396) (uvalueMInt (extract (shl v_6399 3) 0 (bitwidthMInt v_6399)))) 128 256);
      pure ()
    pat_end;
    pattern fun (v_3179 : imm int) (v_3178 : Mem) (v_3180 : reg (bv 128)) => do
      v_10466 <- getRegister v_3180;
      v_10467 <- evaluateAddress v_3178;
      v_10468 <- load v_10467 16;
      v_10471 <- eval (concat (expression.bv_nat 248 0) (handleImmediateWithSignExtend v_3179 8 8));
      setRegister (lhs.of_reg v_3180) (extract (lshr (concat v_10466 v_10468) (uvalueMInt (extract (shl v_10471 3) 0 (bitwidthMInt v_10471)))) 128 256);
      pure ()
    pat_end
