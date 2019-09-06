def vpsubd1 : instruction :=
  definst "vpsubd" $ do
    pattern fun (v_2499 : reg (bv 128)) (v_2500 : reg (bv 128)) (v_2501 : reg (bv 128)) => do
      v_4212 <- getRegister v_2500;
      v_4214 <- getRegister v_2499;
      setRegister (lhs.of_reg v_2501) (concat (sub (extract v_4212 0 32) (extract v_4214 0 32)) (concat (sub (extract v_4212 32 64) (extract v_4214 32 64)) (concat (sub (extract v_4212 64 96) (extract v_4214 64 96)) (sub (extract v_4212 96 128) (extract v_4214 96 128)))));
      pure ()
    pat_end;
    pattern fun (v_2510 : reg (bv 256)) (v_2511 : reg (bv 256)) (v_2512 : reg (bv 256)) => do
      v_4235 <- getRegister v_2511;
      v_4237 <- getRegister v_2510;
      setRegister (lhs.of_reg v_2512) (concat (sub (extract v_4235 0 32) (extract v_4237 0 32)) (concat (sub (extract v_4235 32 64) (extract v_4237 32 64)) (concat (sub (extract v_4235 64 96) (extract v_4237 64 96)) (concat (sub (extract v_4235 96 128) (extract v_4237 96 128)) (concat (sub (extract v_4235 128 160) (extract v_4237 128 160)) (concat (sub (extract v_4235 160 192) (extract v_4237 160 192)) (concat (sub (extract v_4235 192 224) (extract v_4237 192 224)) (sub (extract v_4235 224 256) (extract v_4237 224 256)))))))));
      pure ()
    pat_end;
    pattern fun (v_2493 : Mem) (v_2494 : reg (bv 128)) (v_2495 : reg (bv 128)) => do
      v_10364 <- getRegister v_2494;
      v_10366 <- evaluateAddress v_2493;
      v_10367 <- load v_10366 16;
      setRegister (lhs.of_reg v_2495) (concat (sub (extract v_10364 0 32) (extract v_10367 0 32)) (concat (sub (extract v_10364 32 64) (extract v_10367 32 64)) (concat (sub (extract v_10364 64 96) (extract v_10367 64 96)) (sub (extract v_10364 96 128) (extract v_10367 96 128)))));
      pure ()
    pat_end;
    pattern fun (v_2504 : Mem) (v_2505 : reg (bv 256)) (v_2506 : reg (bv 256)) => do
      v_10383 <- getRegister v_2505;
      v_10385 <- evaluateAddress v_2504;
      v_10386 <- load v_10385 32;
      setRegister (lhs.of_reg v_2506) (concat (sub (extract v_10383 0 32) (extract v_10386 0 32)) (concat (sub (extract v_10383 32 64) (extract v_10386 32 64)) (concat (sub (extract v_10383 64 96) (extract v_10386 64 96)) (concat (sub (extract v_10383 96 128) (extract v_10386 96 128)) (concat (sub (extract v_10383 128 160) (extract v_10386 128 160)) (concat (sub (extract v_10383 160 192) (extract v_10386 160 192)) (concat (sub (extract v_10383 192 224) (extract v_10386 192 224)) (sub (extract v_10383 224 256) (extract v_10386 224 256)))))))));
      pure ()
    pat_end
