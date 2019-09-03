def vpermq1 : instruction :=
  definst "vpermq" $ do
    pattern fun (v_3095 : imm int) (v_3097 : reg (bv 256)) (v_3098 : reg (bv 256)) => do
      v_8685 <- getRegister v_3097;
      v_8686 <- eval (handleImmediateWithSignExtend v_3095 8 8);
      setRegister (lhs.of_reg v_3098) (concat (extract (lshr v_8685 (uvalueMInt (extract (shl (concat (expression.bv_nat 254 0) (extract v_8686 0 2)) 6) 0 256))) 192 256) (concat (extract (lshr v_8685 (uvalueMInt (extract (shl (concat (expression.bv_nat 254 0) (extract v_8686 2 4)) 6) 0 256))) 192 256) (concat (extract (lshr v_8685 (uvalueMInt (extract (shl (concat (expression.bv_nat 254 0) (extract v_8686 4 6)) 6) 0 256))) 192 256) (extract (lshr v_8685 (uvalueMInt (extract (shl (concat (expression.bv_nat 254 0) (extract v_8686 6 8)) 6) 0 256))) 192 256))));
      pure ()
    pat_end;
    pattern fun (v_3091 : imm int) (v_3090 : Mem) (v_3092 : reg (bv 256)) => do
      v_17431 <- evaluateAddress v_3090;
      v_17432 <- load v_17431 32;
      v_17433 <- eval (handleImmediateWithSignExtend v_3091 8 8);
      setRegister (lhs.of_reg v_3092) (concat (extract (lshr v_17432 (uvalueMInt (extract (shl (concat (expression.bv_nat 254 0) (extract v_17433 0 2)) 6) 0 256))) 192 256) (concat (extract (lshr v_17432 (uvalueMInt (extract (shl (concat (expression.bv_nat 254 0) (extract v_17433 2 4)) 6) 0 256))) 192 256) (concat (extract (lshr v_17432 (uvalueMInt (extract (shl (concat (expression.bv_nat 254 0) (extract v_17433 4 6)) 6) 0 256))) 192 256) (extract (lshr v_17432 (uvalueMInt (extract (shl (concat (expression.bv_nat 254 0) (extract v_17433 6 8)) 6) 0 256))) 192 256))));
      pure ()
    pat_end
