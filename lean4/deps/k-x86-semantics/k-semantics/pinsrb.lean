def pinsrb1 : instruction :=
  definst "pinsrb" $ do
    pattern fun (v_2506 : imm int) (v_2509 : reg (bv 32)) (v_2507 : reg (bv 128)) => do
      v_4387 <- getRegister v_2507;
      v_4393 <- eval (uvalueMInt (extract (shl (concat (expression.bv_nat 124 0) (extract (handleImmediateWithSignExtend v_2506 8 8) 4 8)) 3) 0 128));
      v_4395 <- eval (extract (shl (expression.bv_nat 128 255) v_4393) 0 128);
      v_4398 <- getRegister v_2509;
      setRegister (lhs.of_reg v_2507) (bv_or (bv_and v_4387 (bv_xor v_4395 (expression.bv_nat 128 340282366920938463463374607431768211455))) (bv_and (extract (shl (concat (expression.bv_nat 96 0) v_4398) v_4393) 0 128) v_4395));
      pure ()
    pat_end;
    pattern fun (v_2502 : imm int) (v_2501 : Mem) (v_2503 : reg (bv 128)) => do
      v_11499 <- getRegister v_2503;
      v_11505 <- eval (uvalueMInt (extract (shl (concat (expression.bv_nat 124 0) (extract (handleImmediateWithSignExtend v_2502 8 8) 4 8)) 3) 0 128));
      v_11507 <- eval (extract (shl (expression.bv_nat 128 255) v_11505) 0 128);
      v_11510 <- evaluateAddress v_2501;
      v_11511 <- load v_11510 1;
      setRegister (lhs.of_reg v_2503) (bv_or (bv_and v_11499 (bv_xor v_11507 (expression.bv_nat 128 340282366920938463463374607431768211455))) (bv_and (extract (shl (concat (expression.bv_nat 120 0) v_11511) v_11505) 0 128) v_11507));
      pure ()
    pat_end
