def psllw1 : instruction :=
  definst "psllw" $ do
    pattern fun (v_3052 : imm int) (v_3051 : reg (bv 128)) => do
      v_7619 <- eval (handleImmediateWithSignExtend v_3052 8 8);
      v_7622 <- getRegister v_3051;
      v_7624 <- eval (concat (expression.bv_nat 8 0) v_7619);
      setRegister (lhs.of_reg v_3051) (mux (ugt (concat (expression.bv_nat 56 0) v_7619) (expression.bv_nat 64 15)) (expression.bv_nat 128 0) (concat (extract (shl (extract v_7622 0 16) v_7624) 0 16) (concat (extract (shl (extract v_7622 16 32) v_7624) 0 16) (concat (extract (shl (extract v_7622 32 48) v_7624) 0 16) (concat (extract (shl (extract v_7622 48 64) v_7624) 0 16) (concat (extract (shl (extract v_7622 64 80) v_7624) 0 16) (concat (extract (shl (extract v_7622 80 96) v_7624) 0 16) (concat (extract (shl (extract v_7622 96 112) v_7624) 0 16) (extract (shl (extract v_7622 112 128) v_7624) 0 16)))))))));
      pure ()
    pat_end;
    pattern fun (v_3060 : reg (bv 128)) (v_3061 : reg (bv 128)) => do
      v_7661 <- getRegister v_3060;
      v_7664 <- getRegister v_3061;
      v_7666 <- eval (extract v_7661 112 128);
      setRegister (lhs.of_reg v_3061) (mux (ugt (extract v_7661 64 128) (expression.bv_nat 64 15)) (expression.bv_nat 128 0) (concat (extract (shl (extract v_7664 0 16) v_7666) 0 16) (concat (extract (shl (extract v_7664 16 32) v_7666) 0 16) (concat (extract (shl (extract v_7664 32 48) v_7666) 0 16) (concat (extract (shl (extract v_7664 48 64) v_7666) 0 16) (concat (extract (shl (extract v_7664 64 80) v_7666) 0 16) (concat (extract (shl (extract v_7664 80 96) v_7666) 0 16) (concat (extract (shl (extract v_7664 96 112) v_7666) 0 16) (extract (shl (extract v_7664 112 128) v_7666) 0 16)))))))));
      pure ()
    pat_end;
    pattern fun (v_3057 : Mem) (v_3056 : reg (bv 128)) => do
      v_14276 <- evaluateAddress v_3057;
      v_14277 <- load v_14276 16;
      v_14280 <- getRegister v_3056;
      v_14282 <- eval (extract v_14277 112 128);
      setRegister (lhs.of_reg v_3056) (mux (ugt (extract v_14277 64 128) (expression.bv_nat 64 15)) (expression.bv_nat 128 0) (concat (extract (shl (extract v_14280 0 16) v_14282) 0 16) (concat (extract (shl (extract v_14280 16 32) v_14282) 0 16) (concat (extract (shl (extract v_14280 32 48) v_14282) 0 16) (concat (extract (shl (extract v_14280 48 64) v_14282) 0 16) (concat (extract (shl (extract v_14280 64 80) v_14282) 0 16) (concat (extract (shl (extract v_14280 80 96) v_14282) 0 16) (concat (extract (shl (extract v_14280 96 112) v_14282) 0 16) (extract (shl (extract v_14280 112 128) v_14282) 0 16)))))))));
      pure ()
    pat_end
