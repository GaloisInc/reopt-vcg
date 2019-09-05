def vpsrlvd1 : instruction :=
  definst "vpsrlvd" $ do
    pattern fun (v_3432 : reg (bv 128)) (v_3433 : reg (bv 128)) (v_3434 : reg (bv 128)) => do
      v_8771 <- getRegister v_3433;
      v_8773 <- getRegister v_3432;
      setRegister (lhs.of_reg v_3434) (concat (lshr (extract v_8771 0 32) (extract v_8773 0 32)) (concat (lshr (extract v_8771 32 64) (extract v_8773 32 64)) (concat (lshr (extract v_8771 64 96) (extract v_8773 64 96)) (lshr (extract v_8771 96 128) (extract v_8773 96 128)))));
      pure ()
    pat_end;
    pattern fun (v_3443 : reg (bv 256)) (v_3444 : reg (bv 256)) (v_3445 : reg (bv 256)) => do
      v_8794 <- getRegister v_3444;
      v_8796 <- getRegister v_3443;
      setRegister (lhs.of_reg v_3445) (concat (lshr (extract v_8794 0 32) (extract v_8796 0 32)) (concat (lshr (extract v_8794 32 64) (extract v_8796 32 64)) (concat (lshr (extract v_8794 64 96) (extract v_8796 64 96)) (concat (lshr (extract v_8794 96 128) (extract v_8796 96 128)) (concat (lshr (extract v_8794 128 160) (extract v_8796 128 160)) (concat (lshr (extract v_8794 160 192) (extract v_8796 160 192)) (concat (lshr (extract v_8794 192 224) (extract v_8796 192 224)) (lshr (extract v_8794 224 256) (extract v_8796 224 256)))))))));
      pure ()
    pat_end;
    pattern fun (v_3426 : Mem) (v_3427 : reg (bv 128)) (v_3428 : reg (bv 128)) => do
      v_14508 <- getRegister v_3427;
      v_14510 <- evaluateAddress v_3426;
      v_14511 <- load v_14510 16;
      setRegister (lhs.of_reg v_3428) (concat (lshr (extract v_14508 0 32) (extract v_14511 0 32)) (concat (lshr (extract v_14508 32 64) (extract v_14511 32 64)) (concat (lshr (extract v_14508 64 96) (extract v_14511 64 96)) (lshr (extract v_14508 96 128) (extract v_14511 96 128)))));
      pure ()
    pat_end;
    pattern fun (v_3437 : Mem) (v_3438 : reg (bv 256)) (v_3439 : reg (bv 256)) => do
      v_14527 <- getRegister v_3438;
      v_14529 <- evaluateAddress v_3437;
      v_14530 <- load v_14529 32;
      setRegister (lhs.of_reg v_3439) (concat (lshr (extract v_14527 0 32) (extract v_14530 0 32)) (concat (lshr (extract v_14527 32 64) (extract v_14530 32 64)) (concat (lshr (extract v_14527 64 96) (extract v_14530 64 96)) (concat (lshr (extract v_14527 96 128) (extract v_14530 96 128)) (concat (lshr (extract v_14527 128 160) (extract v_14530 128 160)) (concat (lshr (extract v_14527 160 192) (extract v_14530 160 192)) (concat (lshr (extract v_14527 192 224) (extract v_14530 192 224)) (lshr (extract v_14527 224 256) (extract v_14530 224 256)))))))));
      pure ()
    pat_end
