def pminuw1 : instruction :=
  definst "pminuw" $ do
    pattern fun (v_2661 : reg (bv 128)) (v_2662 : reg (bv 128)) => do
      v_5287 <- getRegister v_2662;
      v_5288 <- eval (extract v_5287 0 16);
      v_5289 <- getRegister v_2661;
      v_5290 <- eval (extract v_5289 0 16);
      v_5293 <- eval (extract v_5287 16 32);
      v_5294 <- eval (extract v_5289 16 32);
      v_5297 <- eval (extract v_5287 32 48);
      v_5298 <- eval (extract v_5289 32 48);
      v_5301 <- eval (extract v_5287 48 64);
      v_5302 <- eval (extract v_5289 48 64);
      v_5305 <- eval (extract v_5287 64 80);
      v_5306 <- eval (extract v_5289 64 80);
      v_5309 <- eval (extract v_5287 80 96);
      v_5310 <- eval (extract v_5289 80 96);
      v_5313 <- eval (extract v_5287 96 112);
      v_5314 <- eval (extract v_5289 96 112);
      v_5317 <- eval (extract v_5287 112 128);
      v_5318 <- eval (extract v_5289 112 128);
      setRegister (lhs.of_reg v_2662) (concat (mux (ult v_5288 v_5290) v_5288 v_5290) (concat (mux (ult v_5293 v_5294) v_5293 v_5294) (concat (mux (ult v_5297 v_5298) v_5297 v_5298) (concat (mux (ult v_5301 v_5302) v_5301 v_5302) (concat (mux (ult v_5305 v_5306) v_5305 v_5306) (concat (mux (ult v_5309 v_5310) v_5309 v_5310) (concat (mux (ult v_5313 v_5314) v_5313 v_5314) (mux (ult v_5317 v_5318) v_5317 v_5318))))))));
      pure ()
    pat_end;
    pattern fun (v_2657 : Mem) (v_2658 : reg (bv 128)) => do
      v_12331 <- getRegister v_2658;
      v_12332 <- eval (extract v_12331 0 16);
      v_12333 <- evaluateAddress v_2657;
      v_12334 <- load v_12333 16;
      v_12335 <- eval (extract v_12334 0 16);
      v_12338 <- eval (extract v_12331 16 32);
      v_12339 <- eval (extract v_12334 16 32);
      v_12342 <- eval (extract v_12331 32 48);
      v_12343 <- eval (extract v_12334 32 48);
      v_12346 <- eval (extract v_12331 48 64);
      v_12347 <- eval (extract v_12334 48 64);
      v_12350 <- eval (extract v_12331 64 80);
      v_12351 <- eval (extract v_12334 64 80);
      v_12354 <- eval (extract v_12331 80 96);
      v_12355 <- eval (extract v_12334 80 96);
      v_12358 <- eval (extract v_12331 96 112);
      v_12359 <- eval (extract v_12334 96 112);
      v_12362 <- eval (extract v_12331 112 128);
      v_12363 <- eval (extract v_12334 112 128);
      setRegister (lhs.of_reg v_2658) (concat (mux (ult v_12332 v_12335) v_12332 v_12335) (concat (mux (ult v_12338 v_12339) v_12338 v_12339) (concat (mux (ult v_12342 v_12343) v_12342 v_12343) (concat (mux (ult v_12346 v_12347) v_12346 v_12347) (concat (mux (ult v_12350 v_12351) v_12350 v_12351) (concat (mux (ult v_12354 v_12355) v_12354 v_12355) (concat (mux (ult v_12358 v_12359) v_12358 v_12359) (mux (ult v_12362 v_12363) v_12362 v_12363))))))));
      pure ()
    pat_end
