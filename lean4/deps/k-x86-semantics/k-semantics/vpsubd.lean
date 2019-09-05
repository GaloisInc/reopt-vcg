def vpsubd1 : instruction :=
  definst "vpsubd" $ do
    pattern fun (v_2472 : reg (bv 128)) (v_2473 : reg (bv 128)) (v_2474 : reg (bv 128)) => do
      v_4185 <- getRegister v_2473;
      v_4187 <- getRegister v_2472;
      setRegister (lhs.of_reg v_2474) (concat (sub (extract v_4185 0 32) (extract v_4187 0 32)) (concat (sub (extract v_4185 32 64) (extract v_4187 32 64)) (concat (sub (extract v_4185 64 96) (extract v_4187 64 96)) (sub (extract v_4185 96 128) (extract v_4187 96 128)))));
      pure ()
    pat_end;
    pattern fun (v_2483 : reg (bv 256)) (v_2484 : reg (bv 256)) (v_2485 : reg (bv 256)) => do
      v_4208 <- getRegister v_2484;
      v_4210 <- getRegister v_2483;
      setRegister (lhs.of_reg v_2485) (concat (sub (extract v_4208 0 32) (extract v_4210 0 32)) (concat (sub (extract v_4208 32 64) (extract v_4210 32 64)) (concat (sub (extract v_4208 64 96) (extract v_4210 64 96)) (concat (sub (extract v_4208 96 128) (extract v_4210 96 128)) (concat (sub (extract v_4208 128 160) (extract v_4210 128 160)) (concat (sub (extract v_4208 160 192) (extract v_4210 160 192)) (concat (sub (extract v_4208 192 224) (extract v_4210 192 224)) (sub (extract v_4208 224 256) (extract v_4210 224 256)))))))));
      pure ()
    pat_end;
    pattern fun (v_2466 : Mem) (v_2467 : reg (bv 128)) (v_2468 : reg (bv 128)) => do
      v_10337 <- getRegister v_2467;
      v_10339 <- evaluateAddress v_2466;
      v_10340 <- load v_10339 16;
      setRegister (lhs.of_reg v_2468) (concat (sub (extract v_10337 0 32) (extract v_10340 0 32)) (concat (sub (extract v_10337 32 64) (extract v_10340 32 64)) (concat (sub (extract v_10337 64 96) (extract v_10340 64 96)) (sub (extract v_10337 96 128) (extract v_10340 96 128)))));
      pure ()
    pat_end;
    pattern fun (v_2477 : Mem) (v_2478 : reg (bv 256)) (v_2479 : reg (bv 256)) => do
      v_10356 <- getRegister v_2478;
      v_10358 <- evaluateAddress v_2477;
      v_10359 <- load v_10358 32;
      setRegister (lhs.of_reg v_2479) (concat (sub (extract v_10356 0 32) (extract v_10359 0 32)) (concat (sub (extract v_10356 32 64) (extract v_10359 32 64)) (concat (sub (extract v_10356 64 96) (extract v_10359 64 96)) (concat (sub (extract v_10356 96 128) (extract v_10359 96 128)) (concat (sub (extract v_10356 128 160) (extract v_10359 128 160)) (concat (sub (extract v_10356 160 192) (extract v_10359 160 192)) (concat (sub (extract v_10356 192 224) (extract v_10359 192 224)) (sub (extract v_10356 224 256) (extract v_10359 224 256)))))))));
      pure ()
    pat_end
