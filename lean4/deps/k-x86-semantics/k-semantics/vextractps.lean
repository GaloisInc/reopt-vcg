def vextractps1 : instruction :=
  definst "vextractps" $ do
    pattern fun (v_2497 : imm int) (v_2496 : reg (bv 128)) (v_2498 : reg (bv 32)) => do
      v_4114 <- getRegister v_2496;
      setRegister (lhs.of_reg v_2498) (extract (lshr v_4114 (extract (shl (concat (expression.bv_nat 126 0) (extract (handleImmediateWithSignExtend v_2497 8 8) 6 8)) (expression.bv_nat 128 5)) 0 128)) 96 128);
      pure ()
    pat_end;
    pattern fun (v_2493 : imm int) (v_2491 : reg (bv 128)) (v_2492 : Mem) => do
      v_13864 <- evaluateAddress v_2492;
      v_13865 <- getRegister v_2491;
      store v_13864 (extract (lshr v_13865 (extract (shl (concat (expression.bv_nat 126 0) (extract (handleImmediateWithSignExtend v_2493 8 8) 6 8)) (expression.bv_nat 128 5)) 0 128)) 96 128) 4;
      pure ()
    pat_end
