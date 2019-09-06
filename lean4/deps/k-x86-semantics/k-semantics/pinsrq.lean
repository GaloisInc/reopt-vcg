def pinsrq1 : instruction :=
  definst "pinsrq" $ do
    pattern fun (v_2600 : imm int) (v_2601 : reg (bv 64)) (v_2602 : reg (bv 128)) => do
      v_4504 <- getRegister v_2602;
      v_4509 <- eval (extract (shl (concat (expression.bv_nat 127 0) (extract (handleImmediateWithSignExtend v_2600 8 8) 7 8)) (expression.bv_nat 128 6)) 0 128);
      v_4510 <- eval (shl (expression.bv_nat 128 18446744073709551615) v_4509);
      v_4514 <- getRegister v_2601;
      setRegister (lhs.of_reg v_2602) (bv_or (bv_and v_4504 (bv_xor (extract v_4510 0 128) (expression.bv_nat 128 340282366920938463463374607431768211455))) (extract (bv_and (shl (concat (expression.bv_nat 64 0) v_4514) v_4509) v_4510) 0 128));
      pure ()
    pat_end
