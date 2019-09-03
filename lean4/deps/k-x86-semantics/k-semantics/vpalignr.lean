def vpalignr1 : instruction :=
  definst "vpalignr" $ do
    pattern fun (v_2494 : imm int) (v_2498 : reg (bv 128)) (v_2499 : reg (bv 128)) (v_2500 : reg (bv 128)) => do
      v_5822 <- getRegister v_2499;
      v_5823 <- getRegister v_2498;
      v_5826 <- eval (concat (expression.bv_nat 248 0) (handleImmediateWithSignExtend v_2494 8 8));
      setRegister (lhs.of_reg v_2500) (extract (lshr (concat v_5822 v_5823) (uvalueMInt (extract (shl v_5826 3) 0 (bitwidthMInt v_5826)))) 128 256);
      pure ()
    pat_end;
    pattern fun (v_2507 : imm int) (v_2511 : reg (bv 256)) (v_2512 : reg (bv 256)) (v_2513 : reg (bv 256)) => do
      v_5840 <- getRegister v_2512;
      v_5842 <- getRegister v_2511;
      v_5846 <- eval (concat (expression.bv_nat 248 0) (handleImmediateWithSignExtend v_2507 8 8));
      v_5850 <- eval (uvalueMInt (extract (shl v_5846 3) 0 (bitwidthMInt v_5846)));
      setRegister (lhs.of_reg v_2513) (concat (extract (lshr (concat (extract v_5840 0 128) (extract v_5842 0 128)) v_5850) 128 256) (extract (lshr (concat (extract v_5840 128 256) (extract v_5842 128 256)) v_5850) 128 256));
      pure ()
    pat_end;
    pattern fun (v_2488 : imm int) (v_2491 : Mem) (v_2492 : reg (bv 128)) (v_2493 : reg (bv 128)) => do
      v_15161 <- getRegister v_2492;
      v_15162 <- evaluateAddress v_2491;
      v_15163 <- load v_15162 16;
      v_15166 <- eval (concat (expression.bv_nat 248 0) (handleImmediateWithSignExtend v_2488 8 8));
      setRegister (lhs.of_reg v_2493) (extract (lshr (concat v_15161 v_15163) (uvalueMInt (extract (shl v_15166 3) 0 (bitwidthMInt v_15166)))) 128 256);
      pure ()
    pat_end;
    pattern fun (v_2501 : imm int) (v_2504 : Mem) (v_2505 : reg (bv 256)) (v_2506 : reg (bv 256)) => do
      v_15174 <- getRegister v_2505;
      v_15176 <- evaluateAddress v_2504;
      v_15177 <- load v_15176 32;
      v_15181 <- eval (concat (expression.bv_nat 248 0) (handleImmediateWithSignExtend v_2501 8 8));
      v_15185 <- eval (uvalueMInt (extract (shl v_15181 3) 0 (bitwidthMInt v_15181)));
      setRegister (lhs.of_reg v_2506) (concat (extract (lshr (concat (extract v_15174 0 128) (extract v_15177 0 128)) v_15185) 128 256) (extract (lshr (concat (extract v_15174 128 256) (extract v_15177 128 256)) v_15185) 128 256));
      pure ()
    pat_end
