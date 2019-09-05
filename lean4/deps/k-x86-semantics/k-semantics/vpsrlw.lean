def vpsrlw1 : instruction :=
  definst "vpsrlw" $ do
    pattern fun (v_3468 : imm int) (v_3472 : reg (bv 128)) (v_3473 : reg (bv 128)) => do
      v_8866 <- eval (handleImmediateWithSignExtend v_3468 8 8);
      v_8869 <- getRegister v_3472;
      v_8871 <- eval (concat (expression.bv_nat 8 0) v_8866);
      setRegister (lhs.of_reg v_3473) (mux (ugt (concat (expression.bv_nat 56 0) v_8866) (expression.bv_nat 64 15)) (expression.bv_nat 128 0) (concat (lshr (extract v_8869 0 16) v_8871) (concat (lshr (extract v_8869 16 32) v_8871) (concat (lshr (extract v_8869 32 48) v_8871) (concat (lshr (extract v_8869 48 64) v_8871) (concat (lshr (extract v_8869 64 80) v_8871) (concat (lshr (extract v_8869 80 96) v_8871) (concat (lshr (extract v_8869 96 112) v_8871) (lshr (extract v_8869 112 128) v_8871)))))))));
      pure ()
    pat_end;
    pattern fun (v_3482 : reg (bv 128)) (v_3483 : reg (bv 128)) (v_3484 : reg (bv 128)) => do
      v_8901 <- getRegister v_3482;
      v_8904 <- getRegister v_3483;
      v_8906 <- eval (extract v_8901 112 128);
      setRegister (lhs.of_reg v_3484) (mux (ugt (extract v_8901 64 128) (expression.bv_nat 64 15)) (expression.bv_nat 128 0) (concat (lshr (extract v_8904 0 16) v_8906) (concat (lshr (extract v_8904 16 32) v_8906) (concat (lshr (extract v_8904 32 48) v_8906) (concat (lshr (extract v_8904 48 64) v_8906) (concat (lshr (extract v_8904 64 80) v_8906) (concat (lshr (extract v_8904 80 96) v_8906) (concat (lshr (extract v_8904 96 112) v_8906) (lshr (extract v_8904 112 128) v_8906)))))))));
      pure ()
    pat_end;
    pattern fun (v_3485 : imm int) (v_3489 : reg (bv 256)) (v_3490 : reg (bv 256)) => do
      v_8931 <- eval (handleImmediateWithSignExtend v_3485 8 8);
      v_8934 <- getRegister v_3489;
      v_8936 <- eval (concat (expression.bv_nat 8 0) v_8931);
      setRegister (lhs.of_reg v_3490) (mux (ugt (concat (expression.bv_nat 56 0) v_8931) (expression.bv_nat 64 15)) (expression.bv_nat 256 0) (concat (lshr (extract v_8934 0 16) v_8936) (concat (lshr (extract v_8934 16 32) v_8936) (concat (lshr (extract v_8934 32 48) v_8936) (concat (lshr (extract v_8934 48 64) v_8936) (concat (lshr (extract v_8934 64 80) v_8936) (concat (lshr (extract v_8934 80 96) v_8936) (concat (lshr (extract v_8934 96 112) v_8936) (concat (lshr (extract v_8934 112 128) v_8936) (concat (lshr (extract v_8934 128 144) v_8936) (concat (lshr (extract v_8934 144 160) v_8936) (concat (lshr (extract v_8934 160 176) v_8936) (concat (lshr (extract v_8934 176 192) v_8936) (concat (lshr (extract v_8934 192 208) v_8936) (concat (lshr (extract v_8934 208 224) v_8936) (concat (lshr (extract v_8934 224 240) v_8936) (lshr (extract v_8934 240 256) v_8936)))))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_3501 : reg (bv 128)) (v_3499 : reg (bv 256)) (v_3500 : reg (bv 256)) => do
      v_8990 <- getRegister v_3501;
      v_8993 <- getRegister v_3499;
      v_8995 <- eval (extract v_8990 112 128);
      setRegister (lhs.of_reg v_3500) (mux (ugt (extract v_8990 64 128) (expression.bv_nat 64 15)) (expression.bv_nat 256 0) (concat (lshr (extract v_8993 0 16) v_8995) (concat (lshr (extract v_8993 16 32) v_8995) (concat (lshr (extract v_8993 32 48) v_8995) (concat (lshr (extract v_8993 48 64) v_8995) (concat (lshr (extract v_8993 64 80) v_8995) (concat (lshr (extract v_8993 80 96) v_8995) (concat (lshr (extract v_8993 96 112) v_8995) (concat (lshr (extract v_8993 112 128) v_8995) (concat (lshr (extract v_8993 128 144) v_8995) (concat (lshr (extract v_8993 144 160) v_8995) (concat (lshr (extract v_8993 160 176) v_8995) (concat (lshr (extract v_8993 176 192) v_8995) (concat (lshr (extract v_8993 192 208) v_8995) (concat (lshr (extract v_8993 208 224) v_8995) (concat (lshr (extract v_8993 224 240) v_8995) (lshr (extract v_8993 240 256) v_8995)))))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_3476 : Mem) (v_3477 : reg (bv 128)) (v_3478 : reg (bv 128)) => do
      v_14592 <- evaluateAddress v_3476;
      v_14593 <- load v_14592 16;
      v_14596 <- getRegister v_3477;
      v_14598 <- eval (extract v_14593 112 128);
      setRegister (lhs.of_reg v_3478) (mux (ugt (extract v_14593 64 128) (expression.bv_nat 64 15)) (expression.bv_nat 128 0) (concat (lshr (extract v_14596 0 16) v_14598) (concat (lshr (extract v_14596 16 32) v_14598) (concat (lshr (extract v_14596 32 48) v_14598) (concat (lshr (extract v_14596 48 64) v_14598) (concat (lshr (extract v_14596 64 80) v_14598) (concat (lshr (extract v_14596 80 96) v_14598) (concat (lshr (extract v_14596 96 112) v_14598) (lshr (extract v_14596 112 128) v_14598)))))))));
      pure ()
    pat_end;
    pattern fun (v_3493 : Mem) (v_3494 : reg (bv 256)) (v_3495 : reg (bv 256)) => do
      v_14623 <- evaluateAddress v_3493;
      v_14624 <- load v_14623 16;
      v_14627 <- getRegister v_3494;
      v_14629 <- eval (extract v_14624 112 128);
      setRegister (lhs.of_reg v_3495) (mux (ugt (extract v_14624 64 128) (expression.bv_nat 64 15)) (expression.bv_nat 256 0) (concat (lshr (extract v_14627 0 16) v_14629) (concat (lshr (extract v_14627 16 32) v_14629) (concat (lshr (extract v_14627 32 48) v_14629) (concat (lshr (extract v_14627 48 64) v_14629) (concat (lshr (extract v_14627 64 80) v_14629) (concat (lshr (extract v_14627 80 96) v_14629) (concat (lshr (extract v_14627 96 112) v_14629) (concat (lshr (extract v_14627 112 128) v_14629) (concat (lshr (extract v_14627 128 144) v_14629) (concat (lshr (extract v_14627 144 160) v_14629) (concat (lshr (extract v_14627 160 176) v_14629) (concat (lshr (extract v_14627 176 192) v_14629) (concat (lshr (extract v_14627 192 208) v_14629) (concat (lshr (extract v_14627 208 224) v_14629) (concat (lshr (extract v_14627 224 240) v_14629) (lshr (extract v_14627 240 256) v_14629)))))))))))))))));
      pure ()
    pat_end
