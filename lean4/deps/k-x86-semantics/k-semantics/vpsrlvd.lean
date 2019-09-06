def vpsrlvd1 : instruction :=
  definst "vpsrlvd" $ do
    pattern fun (v_3459 : reg (bv 128)) (v_3460 : reg (bv 128)) (v_3461 : reg (bv 128)) => do
      v_8798 <- getRegister v_3460;
      v_8800 <- getRegister v_3459;
      setRegister (lhs.of_reg v_3461) (concat (lshr (extract v_8798 0 32) (extract v_8800 0 32)) (concat (lshr (extract v_8798 32 64) (extract v_8800 32 64)) (concat (lshr (extract v_8798 64 96) (extract v_8800 64 96)) (lshr (extract v_8798 96 128) (extract v_8800 96 128)))));
      pure ()
    pat_end;
    pattern fun (v_3470 : reg (bv 256)) (v_3471 : reg (bv 256)) (v_3472 : reg (bv 256)) => do
      v_8821 <- getRegister v_3471;
      v_8823 <- getRegister v_3470;
      setRegister (lhs.of_reg v_3472) (concat (lshr (extract v_8821 0 32) (extract v_8823 0 32)) (concat (lshr (extract v_8821 32 64) (extract v_8823 32 64)) (concat (lshr (extract v_8821 64 96) (extract v_8823 64 96)) (concat (lshr (extract v_8821 96 128) (extract v_8823 96 128)) (concat (lshr (extract v_8821 128 160) (extract v_8823 128 160)) (concat (lshr (extract v_8821 160 192) (extract v_8823 160 192)) (concat (lshr (extract v_8821 192 224) (extract v_8823 192 224)) (lshr (extract v_8821 224 256) (extract v_8823 224 256)))))))));
      pure ()
    pat_end;
    pattern fun (v_3453 : Mem) (v_3454 : reg (bv 128)) (v_3455 : reg (bv 128)) => do
      v_14535 <- getRegister v_3454;
      v_14537 <- evaluateAddress v_3453;
      v_14538 <- load v_14537 16;
      setRegister (lhs.of_reg v_3455) (concat (lshr (extract v_14535 0 32) (extract v_14538 0 32)) (concat (lshr (extract v_14535 32 64) (extract v_14538 32 64)) (concat (lshr (extract v_14535 64 96) (extract v_14538 64 96)) (lshr (extract v_14535 96 128) (extract v_14538 96 128)))));
      pure ()
    pat_end;
    pattern fun (v_3464 : Mem) (v_3465 : reg (bv 256)) (v_3466 : reg (bv 256)) => do
      v_14554 <- getRegister v_3465;
      v_14556 <- evaluateAddress v_3464;
      v_14557 <- load v_14556 32;
      setRegister (lhs.of_reg v_3466) (concat (lshr (extract v_14554 0 32) (extract v_14557 0 32)) (concat (lshr (extract v_14554 32 64) (extract v_14557 32 64)) (concat (lshr (extract v_14554 64 96) (extract v_14557 64 96)) (concat (lshr (extract v_14554 96 128) (extract v_14557 96 128)) (concat (lshr (extract v_14554 128 160) (extract v_14557 128 160)) (concat (lshr (extract v_14554 160 192) (extract v_14557 160 192)) (concat (lshr (extract v_14554 192 224) (extract v_14557 192 224)) (lshr (extract v_14554 224 256) (extract v_14557 224 256)))))))));
      pure ()
    pat_end
