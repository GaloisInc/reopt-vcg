def pinsrq1 : instruction :=
  definst "pinsrq" $ do
    pattern fun (v_2523 : imm int) (v_2525 : reg (bv 64)) (v_2524 : reg (bv 128)) => do
      v_4428 <- getRegister v_2524;
      v_4434 <- eval (uvalueMInt (extract (shl (concat (expression.bv_nat 127 0) (extract (handleImmediateWithSignExtend v_2523 8 8) 7 8)) 6) 0 128));
      v_4436 <- eval (extract (shl (expression.bv_nat 128 18446744073709551615) v_4434) 0 128);
      v_4439 <- getRegister v_2525;
      setRegister (lhs.of_reg v_2524) (bv_or (bv_and v_4428 (bv_xor v_4436 (expression.bv_nat 128 340282366920938463463374607431768211455))) (bv_and (extract (shl (concat (expression.bv_nat 64 0) v_4439) v_4434) 0 128) v_4436));
      pure ()
    pat_end
