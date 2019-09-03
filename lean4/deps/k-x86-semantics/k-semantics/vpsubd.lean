def vpsubd1 : instruction :=
  definst "vpsubd" $ do
    pattern fun (v_2408 : reg (bv 128)) (v_2409 : reg (bv 128)) (v_2410 : reg (bv 128)) => do
      v_4121 <- getRegister v_2409;
      v_4123 <- getRegister v_2408;
      setRegister (lhs.of_reg v_2410) (concat (sub (extract v_4121 0 32) (extract v_4123 0 32)) (concat (sub (extract v_4121 32 64) (extract v_4123 32 64)) (concat (sub (extract v_4121 64 96) (extract v_4123 64 96)) (sub (extract v_4121 96 128) (extract v_4123 96 128)))));
      pure ()
    pat_end;
    pattern fun (v_2418 : reg (bv 256)) (v_2419 : reg (bv 256)) (v_2420 : reg (bv 256)) => do
      v_4144 <- getRegister v_2419;
      v_4146 <- getRegister v_2418;
      setRegister (lhs.of_reg v_2420) (concat (sub (extract v_4144 0 32) (extract v_4146 0 32)) (concat (sub (extract v_4144 32 64) (extract v_4146 32 64)) (concat (sub (extract v_4144 64 96) (extract v_4146 64 96)) (concat (sub (extract v_4144 96 128) (extract v_4146 96 128)) (concat (sub (extract v_4144 128 160) (extract v_4146 128 160)) (concat (sub (extract v_4144 160 192) (extract v_4146 160 192)) (concat (sub (extract v_4144 192 224) (extract v_4146 192 224)) (sub (extract v_4144 224 256) (extract v_4146 224 256)))))))));
      pure ()
    pat_end;
    pattern fun (v_2402 : Mem) (v_2403 : reg (bv 128)) (v_2404 : reg (bv 128)) => do
      v_10514 <- getRegister v_2403;
      v_10516 <- evaluateAddress v_2402;
      v_10517 <- load v_10516 16;
      setRegister (lhs.of_reg v_2404) (concat (sub (extract v_10514 0 32) (extract v_10517 0 32)) (concat (sub (extract v_10514 32 64) (extract v_10517 32 64)) (concat (sub (extract v_10514 64 96) (extract v_10517 64 96)) (sub (extract v_10514 96 128) (extract v_10517 96 128)))));
      pure ()
    pat_end;
    pattern fun (v_2413 : Mem) (v_2414 : reg (bv 256)) (v_2415 : reg (bv 256)) => do
      v_10533 <- getRegister v_2414;
      v_10535 <- evaluateAddress v_2413;
      v_10536 <- load v_10535 32;
      setRegister (lhs.of_reg v_2415) (concat (sub (extract v_10533 0 32) (extract v_10536 0 32)) (concat (sub (extract v_10533 32 64) (extract v_10536 32 64)) (concat (sub (extract v_10533 64 96) (extract v_10536 64 96)) (concat (sub (extract v_10533 96 128) (extract v_10536 96 128)) (concat (sub (extract v_10533 128 160) (extract v_10536 128 160)) (concat (sub (extract v_10533 160 192) (extract v_10536 160 192)) (concat (sub (extract v_10533 192 224) (extract v_10536 192 224)) (sub (extract v_10533 224 256) (extract v_10536 224 256)))))))));
      pure ()
    pat_end
