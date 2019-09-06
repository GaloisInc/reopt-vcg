def vpalignr1 : instruction :=
  definst "vpalignr" $ do
    pattern fun (v_2587 : imm int) (v_2588 : reg (bv 128)) (v_2589 : reg (bv 128)) (v_2590 : reg (bv 128)) => do
      v_5697 <- getRegister v_2589;
      v_5698 <- getRegister v_2588;
      setRegister (lhs.of_reg v_2590) (extract (lshr (concat v_5697 v_5698) (extract (shl (concat (expression.bv_nat 248 0) (handleImmediateWithSignExtend v_2587 8 8)) (expression.bv_nat 256 3)) 0 256)) 128 256);
      pure ()
    pat_end;
    pattern fun (v_2600 : imm int) (v_2601 : reg (bv 256)) (v_2602 : reg (bv 256)) (v_2603 : reg (bv 256)) => do
      v_5713 <- getRegister v_2602;
      v_5715 <- getRegister v_2601;
      v_5721 <- eval (extract (shl (concat (expression.bv_nat 248 0) (handleImmediateWithSignExtend v_2600 8 8)) (expression.bv_nat 256 3)) 0 256);
      setRegister (lhs.of_reg v_2603) (concat (extract (lshr (concat (extract v_5713 0 128) (extract v_5715 0 128)) v_5721) 128 256) (extract (lshr (concat (extract v_5713 128 256) (extract v_5715 128 256)) v_5721) 128 256));
      pure ()
    pat_end;
    pattern fun (v_2582 : imm int) (v_2581 : Mem) (v_2583 : reg (bv 128)) (v_2584 : reg (bv 128)) => do
      v_14416 <- getRegister v_2583;
      v_14417 <- evaluateAddress v_2581;
      v_14418 <- load v_14417 16;
      setRegister (lhs.of_reg v_2584) (extract (lshr (concat v_14416 v_14418) (extract (shl (concat (expression.bv_nat 248 0) (handleImmediateWithSignExtend v_2582 8 8)) (expression.bv_nat 256 3)) 0 256)) 128 256);
      pure ()
    pat_end;
    pattern fun (v_2595 : imm int) (v_2594 : Mem) (v_2596 : reg (bv 256)) (v_2597 : reg (bv 256)) => do
      v_14427 <- getRegister v_2596;
      v_14429 <- evaluateAddress v_2594;
      v_14430 <- load v_14429 32;
      v_14436 <- eval (extract (shl (concat (expression.bv_nat 248 0) (handleImmediateWithSignExtend v_2595 8 8)) (expression.bv_nat 256 3)) 0 256);
      setRegister (lhs.of_reg v_2597) (concat (extract (lshr (concat (extract v_14427 0 128) (extract v_14430 0 128)) v_14436) 128 256) (extract (lshr (concat (extract v_14427 128 256) (extract v_14430 128 256)) v_14436) 128 256));
      pure ()
    pat_end
