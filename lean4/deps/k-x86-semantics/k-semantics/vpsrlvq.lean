def vpsrlvq1 : instruction :=
  definst "vpsrlvq" $ do
    pattern fun (v_3454 : reg (bv 128)) (v_3455 : reg (bv 128)) (v_3456 : reg (bv 128)) => do
      v_8833 <- getRegister v_3455;
      v_8835 <- getRegister v_3454;
      setRegister (lhs.of_reg v_3456) (concat (lshr (extract v_8833 0 64) (extract v_8835 0 64)) (lshr (extract v_8833 64 128) (extract v_8835 64 128)));
      pure ()
    pat_end;
    pattern fun (v_3465 : reg (bv 256)) (v_3466 : reg (bv 256)) (v_3467 : reg (bv 256)) => do
      v_8848 <- getRegister v_3466;
      v_8850 <- getRegister v_3465;
      setRegister (lhs.of_reg v_3467) (concat (lshr (extract v_8848 0 64) (extract v_8850 0 64)) (concat (lshr (extract v_8848 64 128) (extract v_8850 64 128)) (concat (lshr (extract v_8848 128 192) (extract v_8850 128 192)) (lshr (extract v_8848 192 256) (extract v_8850 192 256)))));
      pure ()
    pat_end;
    pattern fun (v_3448 : Mem) (v_3449 : reg (bv 128)) (v_3450 : reg (bv 128)) => do
      v_14562 <- getRegister v_3449;
      v_14564 <- evaluateAddress v_3448;
      v_14565 <- load v_14564 16;
      setRegister (lhs.of_reg v_3450) (concat (lshr (extract v_14562 0 64) (extract v_14565 0 64)) (lshr (extract v_14562 64 128) (extract v_14565 64 128)));
      pure ()
    pat_end;
    pattern fun (v_3459 : Mem) (v_3460 : reg (bv 256)) (v_3461 : reg (bv 256)) => do
      v_14573 <- getRegister v_3460;
      v_14575 <- evaluateAddress v_3459;
      v_14576 <- load v_14575 32;
      setRegister (lhs.of_reg v_3461) (concat (lshr (extract v_14573 0 64) (extract v_14576 0 64)) (concat (lshr (extract v_14573 64 128) (extract v_14576 64 128)) (concat (lshr (extract v_14573 128 192) (extract v_14576 128 192)) (lshr (extract v_14573 192 256) (extract v_14576 192 256)))));
      pure ()
    pat_end
