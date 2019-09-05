def vpinsrq1 : instruction :=
  definst "vpinsrq" $ do
    pattern fun (v_3381 : imm int) (v_3382 : reg (bv 64)) (v_3384 : reg (bv 128)) (v_3385 : reg (bv 128)) => do
      v_9646 <- getRegister v_3384;
      v_9651 <- eval (extract (shl (concat (expression.bv_nat 127 0) (extract (handleImmediateWithSignExtend v_3381 8 8) 7 8)) (expression.bv_nat 128 6)) 0 128);
      v_9652 <- eval (shl (expression.bv_nat 128 18446744073709551615) v_9651);
      v_9656 <- getRegister v_3382;
      setRegister (lhs.of_reg v_3385) (bv_or (bv_and v_9646 (bv_xor (extract v_9652 0 128) (expression.bv_nat 128 340282366920938463463374607431768211455))) (extract (bv_and (shl (concat (expression.bv_nat 64 0) v_9656) v_9651) v_9652) 0 128));
      pure ()
    pat_end;
    pattern fun (v_3375 : imm int) (v_3376 : Mem) (v_3377 : reg (bv 128)) (v_3378 : reg (bv 128)) => do
      v_18004 <- getRegister v_3377;
      v_18009 <- eval (extract (shl (concat (expression.bv_nat 127 0) (extract (handleImmediateWithSignExtend v_3375 8 8) 7 8)) (expression.bv_nat 128 6)) 0 128);
      v_18010 <- eval (shl (expression.bv_nat 128 18446744073709551615) v_18009);
      v_18014 <- evaluateAddress v_3376;
      v_18015 <- load v_18014 8;
      setRegister (lhs.of_reg v_3378) (bv_or (bv_and v_18004 (bv_xor (extract v_18010 0 128) (expression.bv_nat 128 340282366920938463463374607431768211455))) (extract (bv_and (shl (concat (expression.bv_nat 64 0) v_18015) v_18009) v_18010) 0 128));
      pure ()
    pat_end
