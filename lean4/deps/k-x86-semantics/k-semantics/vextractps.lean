def vextractps1 : instruction :=
  definst "vextractps" $ do
    pattern fun (v_2421 : imm int) (v_2420 : reg (bv 128)) (v_2423 : reg (bv 32)) => do
      v_4038 <- getRegister v_2420;
      setRegister (lhs.of_reg v_2423) (extract (lshr v_4038 (uvalueMInt (extract (shl (concat (expression.bv_nat 126 0) (extract (handleImmediateWithSignExtend v_2421 8 8) 6 8)) 5) 0 128))) 96 128);
      pure ()
    pat_end;
    pattern fun (v_2416 : imm int) (v_2415 : reg (bv 128)) (v_2417 : Mem) => do
      v_23621 <- evaluateAddress v_2417;
      v_23622 <- getRegister v_2415;
      store v_23621 (extract (lshr v_23622 (uvalueMInt (extract (shl (concat (expression.bv_nat 126 0) (extract (handleImmediateWithSignExtend v_2416 8 8) 6 8)) 5) 0 128))) 96 128) 4;
      pure ()
    pat_end
