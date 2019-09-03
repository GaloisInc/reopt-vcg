def vpalignr1 : instruction :=
  definst "vpalignr" $ do
    pattern fun (v_2512 : imm int) (v_2507 : reg (bv 128)) (v_2508 : reg (bv 128)) (v_2509 : reg (bv 128)) => do
      v_5691 <- getRegister v_2508;
      v_5692 <- getRegister v_2507;
      setRegister (lhs.of_reg v_2509) (extract (lshr (concat v_5691 v_5692) (uvalueMInt (extract (shl (concat (expression.bv_nat 248 0) (handleImmediateWithSignExtend v_2512 8 8)) 3) 0 256))) 128 256);
      pure ()
    pat_end;
    pattern fun (v_2522 : imm int) (v_2524 : reg (bv 256)) (v_2525 : reg (bv 256)) (v_2526 : reg (bv 256)) => do
      v_5708 <- getRegister v_2525;
      v_5710 <- getRegister v_2524;
      v_5717 <- eval (uvalueMInt (extract (shl (concat (expression.bv_nat 248 0) (handleImmediateWithSignExtend v_2522 8 8)) 3) 0 256));
      setRegister (lhs.of_reg v_2526) (concat (extract (lshr (concat (extract v_5708 0 128) (extract v_5710 0 128)) v_5717) 128 256) (extract (lshr (concat (extract v_5708 128 256) (extract v_5710 128 256)) v_5717) 128 256));
      pure ()
    pat_end;
    pattern fun (v_2506 : imm int) (v_2505 : Mem) (v_2501 : reg (bv 128)) (v_2502 : reg (bv 128)) => do
      v_14658 <- getRegister v_2501;
      v_14659 <- evaluateAddress v_2505;
      v_14660 <- load v_14659 16;
      setRegister (lhs.of_reg v_2502) (extract (lshr (concat v_14658 v_14660) (uvalueMInt (extract (shl (concat (expression.bv_nat 248 0) (handleImmediateWithSignExtend v_2506 8 8)) 3) 0 256))) 128 256);
      pure ()
    pat_end;
    pattern fun (v_2517 : imm int) (v_2516 : Mem) (v_2518 : reg (bv 256)) (v_2519 : reg (bv 256)) => do
      v_14670 <- getRegister v_2518;
      v_14672 <- evaluateAddress v_2516;
      v_14673 <- load v_14672 32;
      v_14680 <- eval (uvalueMInt (extract (shl (concat (expression.bv_nat 248 0) (handleImmediateWithSignExtend v_2517 8 8)) 3) 0 256));
      setRegister (lhs.of_reg v_2519) (concat (extract (lshr (concat (extract v_14670 0 128) (extract v_14673 0 128)) v_14680) 128 256) (extract (lshr (concat (extract v_14670 128 256) (extract v_14673 128 256)) v_14680) 128 256));
      pure ()
    pat_end
