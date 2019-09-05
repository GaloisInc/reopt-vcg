def vpalignr1 : instruction :=
  definst "vpalignr" $ do
    pattern fun (v_2560 : imm int) (v_2562 : reg (bv 128)) (v_2563 : reg (bv 128)) (v_2564 : reg (bv 128)) => do
      v_5670 <- getRegister v_2563;
      v_5671 <- getRegister v_2562;
      setRegister (lhs.of_reg v_2564) (extract (lshr (concat v_5670 v_5671) (extract (shl (concat (expression.bv_nat 248 0) (handleImmediateWithSignExtend v_2560 8 8)) (expression.bv_nat 256 3)) 0 256)) 128 256);
      pure ()
    pat_end;
    pattern fun (v_2573 : imm int) (v_2574 : reg (bv 256)) (v_2575 : reg (bv 256)) (v_2576 : reg (bv 256)) => do
      v_5686 <- getRegister v_2575;
      v_5688 <- getRegister v_2574;
      v_5694 <- eval (extract (shl (concat (expression.bv_nat 248 0) (handleImmediateWithSignExtend v_2573 8 8)) (expression.bv_nat 256 3)) 0 256);
      setRegister (lhs.of_reg v_2576) (concat (extract (lshr (concat (extract v_5686 0 128) (extract v_5688 0 128)) v_5694) 128 256) (extract (lshr (concat (extract v_5686 128 256) (extract v_5688 128 256)) v_5694) 128 256));
      pure ()
    pat_end;
    pattern fun (v_2554 : imm int) (v_2555 : Mem) (v_2556 : reg (bv 128)) (v_2557 : reg (bv 128)) => do
      v_14389 <- getRegister v_2556;
      v_14390 <- evaluateAddress v_2555;
      v_14391 <- load v_14390 16;
      setRegister (lhs.of_reg v_2557) (extract (lshr (concat v_14389 v_14391) (extract (shl (concat (expression.bv_nat 248 0) (handleImmediateWithSignExtend v_2554 8 8)) (expression.bv_nat 256 3)) 0 256)) 128 256);
      pure ()
    pat_end;
    pattern fun (v_2567 : imm int) (v_2568 : Mem) (v_2569 : reg (bv 256)) (v_2570 : reg (bv 256)) => do
      v_14400 <- getRegister v_2569;
      v_14402 <- evaluateAddress v_2568;
      v_14403 <- load v_14402 32;
      v_14409 <- eval (extract (shl (concat (expression.bv_nat 248 0) (handleImmediateWithSignExtend v_2567 8 8)) (expression.bv_nat 256 3)) 0 256);
      setRegister (lhs.of_reg v_2570) (concat (extract (lshr (concat (extract v_14400 0 128) (extract v_14403 0 128)) v_14409) 128 256) (extract (lshr (concat (extract v_14400 128 256) (extract v_14403 128 256)) v_14409) 128 256));
      pure ()
    pat_end
