def vextractps1 : instruction :=
  definst "vextractps" $ do
    pattern fun (v_2409 : imm int) (v_2408 : reg (bv 128)) (v_2405 : reg (bv 32)) => do
      v_4025 <- getRegister v_2408;
      v_4028 <- eval (concat (expression.bv_nat 126 0) (extract (handleImmediateWithSignExtend v_2409 8 8) 6 8));
      setRegister (lhs.of_reg v_2405) (extract (lshr v_4025 (uvalueMInt (extract (shl v_4028 5) 0 (bitwidthMInt v_4028)))) 96 128);
      pure ()
    pat_end;
    pattern fun (v_2403 : imm int) (v_2402 : reg (bv 128)) (v_2404 : Mem) => do
      v_13745 <- evaluateAddress v_2404;
      v_13746 <- getRegister v_2402;
      v_13749 <- eval (concat (expression.bv_nat 126 0) (extract (handleImmediateWithSignExtend v_2403 8 8) 6 8));
      store v_13745 (extract (lshr v_13746 (uvalueMInt (extract (shl v_13749 5) 0 (bitwidthMInt v_13749)))) 96 128) 4;
      pure ()
    pat_end
