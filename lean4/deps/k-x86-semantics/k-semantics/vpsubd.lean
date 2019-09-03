def vpsubd1 : instruction :=
  definst "vpsubd" $ do
    pattern fun (v_2418 : reg (bv 128)) (v_2419 : reg (bv 128)) (v_2420 : reg (bv 128)) => do
      v_4134 <- getRegister v_2419;
      v_4136 <- getRegister v_2418;
      setRegister (lhs.of_reg v_2420) (concat (sub (extract v_4134 0 32) (extract v_4136 0 32)) (concat (sub (extract v_4134 32 64) (extract v_4136 32 64)) (concat (sub (extract v_4134 64 96) (extract v_4136 64 96)) (sub (extract v_4134 96 128) (extract v_4136 96 128)))));
      pure ()
    pat_end;
    pattern fun (v_2429 : reg (bv 256)) (v_2430 : reg (bv 256)) (v_2431 : reg (bv 256)) => do
      v_4157 <- getRegister v_2430;
      v_4159 <- getRegister v_2429;
      setRegister (lhs.of_reg v_2431) (concat (sub (extract v_4157 0 32) (extract v_4159 0 32)) (concat (sub (extract v_4157 32 64) (extract v_4159 32 64)) (concat (sub (extract v_4157 64 96) (extract v_4159 64 96)) (concat (sub (extract v_4157 96 128) (extract v_4159 96 128)) (concat (sub (extract v_4157 128 160) (extract v_4159 128 160)) (concat (sub (extract v_4157 160 192) (extract v_4159 160 192)) (concat (sub (extract v_4157 192 224) (extract v_4159 192 224)) (sub (extract v_4157 224 256) (extract v_4159 224 256)))))))));
      pure ()
    pat_end;
    pattern fun (v_2413 : Mem) (v_2414 : reg (bv 128)) (v_2415 : reg (bv 128)) => do
      v_10659 <- getRegister v_2414;
      v_10661 <- evaluateAddress v_2413;
      v_10662 <- load v_10661 16;
      setRegister (lhs.of_reg v_2415) (concat (sub (extract v_10659 0 32) (extract v_10662 0 32)) (concat (sub (extract v_10659 32 64) (extract v_10662 32 64)) (concat (sub (extract v_10659 64 96) (extract v_10662 64 96)) (sub (extract v_10659 96 128) (extract v_10662 96 128)))));
      pure ()
    pat_end;
    pattern fun (v_2424 : Mem) (v_2425 : reg (bv 256)) (v_2426 : reg (bv 256)) => do
      v_10678 <- getRegister v_2425;
      v_10680 <- evaluateAddress v_2424;
      v_10681 <- load v_10680 32;
      setRegister (lhs.of_reg v_2426) (concat (sub (extract v_10678 0 32) (extract v_10681 0 32)) (concat (sub (extract v_10678 32 64) (extract v_10681 32 64)) (concat (sub (extract v_10678 64 96) (extract v_10681 64 96)) (concat (sub (extract v_10678 96 128) (extract v_10681 96 128)) (concat (sub (extract v_10678 128 160) (extract v_10681 128 160)) (concat (sub (extract v_10678 160 192) (extract v_10681 160 192)) (concat (sub (extract v_10678 192 224) (extract v_10681 192 224)) (sub (extract v_10678 224 256) (extract v_10681 224 256)))))))));
      pure ()
    pat_end
