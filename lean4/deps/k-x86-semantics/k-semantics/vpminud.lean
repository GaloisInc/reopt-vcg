def vpminud1 : instruction :=
  definst "vpminud" $ do
    pattern fun (v_2528 : reg (bv 128)) (v_2529 : reg (bv 128)) (v_2530 : reg (bv 128)) => do
      v_4998 <- getRegister v_2529;
      v_4999 <- eval (extract v_4998 0 32);
      v_5000 <- getRegister v_2528;
      v_5001 <- eval (extract v_5000 0 32);
      v_5004 <- eval (extract v_4998 32 64);
      v_5005 <- eval (extract v_5000 32 64);
      v_5008 <- eval (extract v_4998 64 96);
      v_5009 <- eval (extract v_5000 64 96);
      v_5012 <- eval (extract v_4998 96 128);
      v_5013 <- eval (extract v_5000 96 128);
      setRegister (lhs.of_reg v_2530) (concat (mux (ult v_4999 v_5001) v_4999 v_5001) (concat (mux (ult v_5004 v_5005) v_5004 v_5005) (concat (mux (ult v_5008 v_5009) v_5008 v_5009) (mux (ult v_5012 v_5013) v_5012 v_5013))));
      pure ()
    pat_end;
    pattern fun (v_2539 : reg (bv 256)) (v_2540 : reg (bv 256)) (v_2541 : reg (bv 256)) => do
      v_5025 <- getRegister v_2540;
      v_5026 <- eval (extract v_5025 0 32);
      v_5027 <- getRegister v_2539;
      v_5028 <- eval (extract v_5027 0 32);
      v_5031 <- eval (extract v_5025 32 64);
      v_5032 <- eval (extract v_5027 32 64);
      v_5035 <- eval (extract v_5025 64 96);
      v_5036 <- eval (extract v_5027 64 96);
      v_5039 <- eval (extract v_5025 96 128);
      v_5040 <- eval (extract v_5027 96 128);
      v_5043 <- eval (extract v_5025 128 160);
      v_5044 <- eval (extract v_5027 128 160);
      v_5047 <- eval (extract v_5025 160 192);
      v_5048 <- eval (extract v_5027 160 192);
      v_5051 <- eval (extract v_5025 192 224);
      v_5052 <- eval (extract v_5027 192 224);
      v_5055 <- eval (extract v_5025 224 256);
      v_5056 <- eval (extract v_5027 224 256);
      setRegister (lhs.of_reg v_2541) (concat (mux (ult v_5026 v_5028) v_5026 v_5028) (concat (mux (ult v_5031 v_5032) v_5031 v_5032) (concat (mux (ult v_5035 v_5036) v_5035 v_5036) (concat (mux (ult v_5039 v_5040) v_5039 v_5040) (concat (mux (ult v_5043 v_5044) v_5043 v_5044) (concat (mux (ult v_5047 v_5048) v_5047 v_5048) (concat (mux (ult v_5051 v_5052) v_5051 v_5052) (mux (ult v_5055 v_5056) v_5055 v_5056))))))));
      pure ()
    pat_end;
    pattern fun (v_2525 : Mem) (v_2523 : reg (bv 128)) (v_2524 : reg (bv 128)) => do
      v_12390 <- getRegister v_2523;
      v_12391 <- eval (extract v_12390 0 32);
      v_12392 <- evaluateAddress v_2525;
      v_12393 <- load v_12392 16;
      v_12394 <- eval (extract v_12393 0 32);
      v_12397 <- eval (extract v_12390 32 64);
      v_12398 <- eval (extract v_12393 32 64);
      v_12401 <- eval (extract v_12390 64 96);
      v_12402 <- eval (extract v_12393 64 96);
      v_12405 <- eval (extract v_12390 96 128);
      v_12406 <- eval (extract v_12393 96 128);
      setRegister (lhs.of_reg v_2524) (concat (mux (ult v_12391 v_12394) v_12391 v_12394) (concat (mux (ult v_12397 v_12398) v_12397 v_12398) (concat (mux (ult v_12401 v_12402) v_12401 v_12402) (mux (ult v_12405 v_12406) v_12405 v_12406))));
      pure ()
    pat_end;
    pattern fun (v_2534 : Mem) (v_2535 : reg (bv 256)) (v_2536 : reg (bv 256)) => do
      v_12413 <- getRegister v_2535;
      v_12414 <- eval (extract v_12413 0 32);
      v_12415 <- evaluateAddress v_2534;
      v_12416 <- load v_12415 32;
      v_12417 <- eval (extract v_12416 0 32);
      v_12420 <- eval (extract v_12413 32 64);
      v_12421 <- eval (extract v_12416 32 64);
      v_12424 <- eval (extract v_12413 64 96);
      v_12425 <- eval (extract v_12416 64 96);
      v_12428 <- eval (extract v_12413 96 128);
      v_12429 <- eval (extract v_12416 96 128);
      v_12432 <- eval (extract v_12413 128 160);
      v_12433 <- eval (extract v_12416 128 160);
      v_12436 <- eval (extract v_12413 160 192);
      v_12437 <- eval (extract v_12416 160 192);
      v_12440 <- eval (extract v_12413 192 224);
      v_12441 <- eval (extract v_12416 192 224);
      v_12444 <- eval (extract v_12413 224 256);
      v_12445 <- eval (extract v_12416 224 256);
      setRegister (lhs.of_reg v_2536) (concat (mux (ult v_12414 v_12417) v_12414 v_12417) (concat (mux (ult v_12420 v_12421) v_12420 v_12421) (concat (mux (ult v_12424 v_12425) v_12424 v_12425) (concat (mux (ult v_12428 v_12429) v_12428 v_12429) (concat (mux (ult v_12432 v_12433) v_12432 v_12433) (concat (mux (ult v_12436 v_12437) v_12436 v_12437) (concat (mux (ult v_12440 v_12441) v_12440 v_12441) (mux (ult v_12444 v_12445) v_12444 v_12445))))))));
      pure ()
    pat_end
