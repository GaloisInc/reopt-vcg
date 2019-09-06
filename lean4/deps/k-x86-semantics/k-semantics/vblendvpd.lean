def vblendvpd1 : instruction :=
  definst "vblendvpd" $ do
    pattern fun (v_2912 : reg (bv 128)) (v_2913 : reg (bv 128)) (v_2914 : reg (bv 128)) (v_2915 : reg (bv 128)) => do
      v_5355 <- getRegister v_2912;
      v_5357 <- getRegister v_2914;
      v_5359 <- getRegister v_2913;
      setRegister (lhs.of_reg v_2915) (concat (mux (isBitClear v_5355 0) (extract v_5357 0 64) (extract v_5359 0 64)) (mux (isBitClear v_5355 64) (extract v_5357 64 128) (extract v_5359 64 128)));
      pure ()
    pat_end;
    pattern fun (v_2922 : reg (bv 256)) (v_2923 : reg (bv 256)) (v_2924 : reg (bv 256)) (v_2925 : reg (bv 256)) => do
      v_5374 <- getRegister v_2922;
      v_5376 <- getRegister v_2924;
      v_5378 <- getRegister v_2923;
      setRegister (lhs.of_reg v_2925) (concat (mux (isBitClear v_5374 0) (extract v_5376 0 64) (extract v_5378 0 64)) (concat (mux (isBitClear v_5374 64) (extract v_5376 64 128) (extract v_5378 64 128)) (concat (mux (isBitClear v_5374 128) (extract v_5376 128 192) (extract v_5378 128 192)) (mux (isBitClear v_5374 192) (extract v_5376 192 256) (extract v_5378 192 256)))));
      pure ()
    pat_end;
    pattern fun (v_2906 : reg (bv 128)) (v_2903 : Mem) (v_2907 : reg (bv 128)) (v_2908 : reg (bv 128)) => do
      v_9569 <- getRegister v_2906;
      v_9571 <- getRegister v_2907;
      v_9573 <- evaluateAddress v_2903;
      v_9574 <- load v_9573 16;
      setRegister (lhs.of_reg v_2908) (concat (mux (isBitClear v_9569 0) (extract v_9571 0 64) (extract v_9574 0 64)) (mux (isBitClear v_9569 64) (extract v_9571 64 128) (extract v_9574 64 128)));
      pure ()
    pat_end;
    pattern fun (v_2917 : reg (bv 256)) (v_2916 : Mem) (v_2918 : reg (bv 256)) (v_2919 : reg (bv 256)) => do
      v_9583 <- getRegister v_2917;
      v_9585 <- getRegister v_2918;
      v_9587 <- evaluateAddress v_2916;
      v_9588 <- load v_9587 32;
      setRegister (lhs.of_reg v_2919) (concat (mux (isBitClear v_9583 0) (extract v_9585 0 64) (extract v_9588 0 64)) (concat (mux (isBitClear v_9583 64) (extract v_9585 64 128) (extract v_9588 64 128)) (concat (mux (isBitClear v_9583 128) (extract v_9585 128 192) (extract v_9588 128 192)) (mux (isBitClear v_9583 192) (extract v_9585 192 256) (extract v_9588 192 256)))));
      pure ()
    pat_end
