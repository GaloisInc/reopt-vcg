def psllw1 : instruction :=
  definst "psllw" $ do
    pattern fun (v_3002 : imm int) (v_3003 : reg (bv 128)) => do
      v_7622 <- eval (handleImmediateWithSignExtend v_3002 8 8);
      v_7625 <- getRegister v_3003;
      v_7628 <- eval (uvalueMInt (concat (expression.bv_nat 8 0) v_7622));
      setRegister (lhs.of_reg v_3003) (mux (ugt (concat (expression.bv_nat 56 0) v_7622) (expression.bv_nat 64 15)) (expression.bv_nat 128 0) (concat (extract (shl (extract v_7625 0 16) v_7628) 0 16) (concat (extract (shl (extract v_7625 16 32) v_7628) 0 16) (concat (extract (shl (extract v_7625 32 48) v_7628) 0 16) (concat (extract (shl (extract v_7625 48 64) v_7628) 0 16) (concat (extract (shl (extract v_7625 64 80) v_7628) 0 16) (concat (extract (shl (extract v_7625 80 96) v_7628) 0 16) (concat (extract (shl (extract v_7625 96 112) v_7628) 0 16) (extract (shl (extract v_7625 112 128) v_7628) 0 16)))))))));
      pure ()
    pat_end;
    pattern fun (v_3011 : reg (bv 128)) (v_3012 : reg (bv 128)) => do
      v_7665 <- getRegister v_3011;
      v_7668 <- getRegister v_3012;
      v_7671 <- eval (uvalueMInt (extract v_7665 112 128));
      setRegister (lhs.of_reg v_3012) (mux (ugt (extract v_7665 64 128) (expression.bv_nat 64 15)) (expression.bv_nat 128 0) (concat (extract (shl (extract v_7668 0 16) v_7671) 0 16) (concat (extract (shl (extract v_7668 16 32) v_7671) 0 16) (concat (extract (shl (extract v_7668 32 48) v_7671) 0 16) (concat (extract (shl (extract v_7668 48 64) v_7671) 0 16) (concat (extract (shl (extract v_7668 64 80) v_7671) 0 16) (concat (extract (shl (extract v_7668 80 96) v_7671) 0 16) (concat (extract (shl (extract v_7668 96 112) v_7671) 0 16) (extract (shl (extract v_7668 112 128) v_7671) 0 16)))))))));
      pure ()
    pat_end;
    pattern fun (v_3007 : Mem) (v_3008 : reg (bv 128)) => do
      v_14448 <- evaluateAddress v_3007;
      v_14449 <- load v_14448 16;
      v_14452 <- getRegister v_3008;
      v_14455 <- eval (uvalueMInt (extract v_14449 112 128));
      setRegister (lhs.of_reg v_3008) (mux (ugt (extract v_14449 64 128) (expression.bv_nat 64 15)) (expression.bv_nat 128 0) (concat (extract (shl (extract v_14452 0 16) v_14455) 0 16) (concat (extract (shl (extract v_14452 16 32) v_14455) 0 16) (concat (extract (shl (extract v_14452 32 48) v_14455) 0 16) (concat (extract (shl (extract v_14452 48 64) v_14455) 0 16) (concat (extract (shl (extract v_14452 64 80) v_14455) 0 16) (concat (extract (shl (extract v_14452 80 96) v_14455) 0 16) (concat (extract (shl (extract v_14452 96 112) v_14455) 0 16) (extract (shl (extract v_14452 112 128) v_14455) 0 16)))))))));
      pure ()
    pat_end
