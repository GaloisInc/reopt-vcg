def pinsrq1 : instruction :=
  definst "pinsrq" $ do
    pattern fun (v_2510 : imm int) (v_2512 : reg (bv 64)) (v_2509 : reg (bv 128)) => do
      v_4455 <- getRegister v_2509;
      v_4458 <- eval (concat (expression.bv_nat 127 0) (extract (handleImmediateWithSignExtend v_2510 8 8) 7 8));
      v_4462 <- eval (uvalueMInt (extract (shl v_4458 6) 0 (bitwidthMInt v_4458)));
      v_4464 <- eval (extract (shl (expression.bv_nat 128 18446744073709551615) v_4462) 0 128);
      v_4469 <- getRegister v_2512;
      v_4470 <- eval (concat (expression.bv_nat 64 0) v_4469);
      setRegister (lhs.of_reg v_2509) (bv_or (bv_and v_4455 (bv_xor v_4464 (mi (bitwidthMInt v_4464) -1))) (bv_and (extract (shl v_4470 v_4462) 0 (bitwidthMInt v_4470)) v_4464));
      pure ()
    pat_end
