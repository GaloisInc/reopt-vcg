def vpsrlvd1 : instruction :=
  definst "vpsrlvd" $ do
    pattern fun (v_3379 : reg (bv 128)) (v_3380 : reg (bv 128)) (v_3381 : reg (bv 128)) => do
      v_8954 <- getRegister v_3380;
      v_8956 <- getRegister v_3379;
      setRegister (lhs.of_reg v_3381) (concat (lshr (extract v_8954 0 32) (uvalueMInt (extract v_8956 0 32))) (concat (lshr (extract v_8954 32 64) (uvalueMInt (extract v_8956 32 64))) (concat (lshr (extract v_8954 64 96) (uvalueMInt (extract v_8956 64 96))) (lshr (extract v_8954 96 128) (uvalueMInt (extract v_8956 96 128))))));
      pure ()
    pat_end;
    pattern fun (v_3391 : reg (bv 256)) (v_3392 : reg (bv 256)) (v_3393 : reg (bv 256)) => do
      v_8981 <- getRegister v_3392;
      v_8983 <- getRegister v_3391;
      setRegister (lhs.of_reg v_3393) (concat (lshr (extract v_8981 0 32) (uvalueMInt (extract v_8983 0 32))) (concat (lshr (extract v_8981 32 64) (uvalueMInt (extract v_8983 32 64))) (concat (lshr (extract v_8981 64 96) (uvalueMInt (extract v_8983 64 96))) (concat (lshr (extract v_8981 96 128) (uvalueMInt (extract v_8983 96 128))) (concat (lshr (extract v_8981 128 160) (uvalueMInt (extract v_8983 128 160))) (concat (lshr (extract v_8981 160 192) (uvalueMInt (extract v_8983 160 192))) (concat (lshr (extract v_8981 192 224) (uvalueMInt (extract v_8983 192 224))) (lshr (extract v_8981 224 256) (uvalueMInt (extract v_8983 224 256))))))))));
      pure ()
    pat_end;
    pattern fun (v_3373 : Mem) (v_3374 : reg (bv 128)) (v_3375 : reg (bv 128)) => do
      v_14853 <- getRegister v_3374;
      v_14855 <- evaluateAddress v_3373;
      v_14856 <- load v_14855 16;
      setRegister (lhs.of_reg v_3375) (concat (lshr (extract v_14853 0 32) (uvalueMInt (extract v_14856 0 32))) (concat (lshr (extract v_14853 32 64) (uvalueMInt (extract v_14856 32 64))) (concat (lshr (extract v_14853 64 96) (uvalueMInt (extract v_14856 64 96))) (lshr (extract v_14853 96 128) (uvalueMInt (extract v_14856 96 128))))));
      pure ()
    pat_end;
    pattern fun (v_3384 : Mem) (v_3386 : reg (bv 256)) (v_3387 : reg (bv 256)) => do
      v_14876 <- getRegister v_3386;
      v_14878 <- evaluateAddress v_3384;
      v_14879 <- load v_14878 32;
      setRegister (lhs.of_reg v_3387) (concat (lshr (extract v_14876 0 32) (uvalueMInt (extract v_14879 0 32))) (concat (lshr (extract v_14876 32 64) (uvalueMInt (extract v_14879 32 64))) (concat (lshr (extract v_14876 64 96) (uvalueMInt (extract v_14879 64 96))) (concat (lshr (extract v_14876 96 128) (uvalueMInt (extract v_14879 96 128))) (concat (lshr (extract v_14876 128 160) (uvalueMInt (extract v_14879 128 160))) (concat (lshr (extract v_14876 160 192) (uvalueMInt (extract v_14879 160 192))) (concat (lshr (extract v_14876 192 224) (uvalueMInt (extract v_14879 192 224))) (lshr (extract v_14876 224 256) (uvalueMInt (extract v_14879 224 256))))))))));
      pure ()
    pat_end
