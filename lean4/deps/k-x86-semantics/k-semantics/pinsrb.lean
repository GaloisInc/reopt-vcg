def pinsrb1 : instruction :=
  definst "pinsrb" $ do
    pattern fun (v_2493 : imm int) (v_2494 : reg (bv 32)) (v_2492 : reg (bv 128)) => do
      v_4406 <- getRegister v_2492;
      v_4409 <- eval (concat (expression.bv_nat 124 0) (extract (handleImmediateWithSignExtend v_2493 8 8) 4 8));
      v_4413 <- eval (uvalueMInt (extract (shl v_4409 3) 0 (bitwidthMInt v_4409)));
      v_4415 <- eval (extract (shl (expression.bv_nat 128 255) v_4413) 0 128);
      v_4420 <- getRegister v_2494;
      v_4421 <- eval (concat (expression.bv_nat 96 0) v_4420);
      setRegister (lhs.of_reg v_2492) (bv_or (bv_and v_4406 (bv_xor v_4415 (mi (bitwidthMInt v_4415) -1))) (bv_and (extract (shl v_4421 v_4413) 0 (bitwidthMInt v_4421)) v_4415));
      pure ()
    pat_end;
    pattern fun (v_2488 : imm int) (v_2486 : Mem) (v_2487 : reg (bv 128)) => do
      v_11848 <- getRegister v_2487;
      v_11851 <- eval (concat (expression.bv_nat 124 0) (extract (handleImmediateWithSignExtend v_2488 8 8) 4 8));
      v_11855 <- eval (uvalueMInt (extract (shl v_11851 3) 0 (bitwidthMInt v_11851)));
      v_11857 <- eval (extract (shl (expression.bv_nat 128 255) v_11855) 0 128);
      v_11862 <- evaluateAddress v_2486;
      v_11863 <- load v_11862 1;
      v_11864 <- eval (concat (expression.bv_nat 120 0) v_11863);
      setRegister (lhs.of_reg v_2487) (bv_or (bv_and v_11848 (bv_xor v_11857 (mi (bitwidthMInt v_11857) -1))) (bv_and (extract (shl v_11864 v_11855) 0 (bitwidthMInt v_11864)) v_11857));
      pure ()
    pat_end
