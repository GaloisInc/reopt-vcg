def palignr1 : instruction :=
  definst "palignr" $ do
    pattern fun (v_3196 : imm int) (v_3197 : reg (bv 128)) (v_3198 : reg (bv 128)) => do
      v_6378 <- getRegister v_3198;
      v_6379 <- getRegister v_3197;
      setRegister (lhs.of_reg v_3198) (extract (lshr (concat v_6378 v_6379) (uvalueMInt (extract (shl (concat (expression.bv_nat 248 0) (handleImmediateWithSignExtend v_3196 8 8)) 3) 0 256))) 128 256);
      pure ()
    pat_end;
    pattern fun (v_3192 : imm int) (v_3191 : Mem) (v_3193 : reg (bv 128)) => do
      v_10437 <- getRegister v_3193;
      v_10438 <- evaluateAddress v_3191;
      v_10439 <- load v_10438 16;
      setRegister (lhs.of_reg v_3193) (extract (lshr (concat v_10437 v_10439) (uvalueMInt (extract (shl (concat (expression.bv_nat 248 0) (handleImmediateWithSignExtend v_3192 8 8)) 3) 0 256))) 128 256);
      pure ()
    pat_end
