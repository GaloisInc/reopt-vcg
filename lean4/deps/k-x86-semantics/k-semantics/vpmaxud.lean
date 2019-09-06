def vpmaxud1 : instruction :=
  definst "vpmaxud" $ do
    pattern fun (v_2499 : reg (bv 128)) (v_2500 : reg (bv 128)) (v_2501 : reg (bv 128)) => do
      v_4252 <- getRegister v_2500;
      v_4253 <- eval (extract v_4252 0 32);
      v_4254 <- getRegister v_2499;
      v_4255 <- eval (extract v_4254 0 32);
      v_4258 <- eval (extract v_4252 32 64);
      v_4259 <- eval (extract v_4254 32 64);
      v_4262 <- eval (extract v_4252 64 96);
      v_4263 <- eval (extract v_4254 64 96);
      v_4266 <- eval (extract v_4252 96 128);
      v_4267 <- eval (extract v_4254 96 128);
      setRegister (lhs.of_reg v_2501) (concat (mux (ugt v_4253 v_4255) v_4253 v_4255) (concat (mux (ugt v_4258 v_4259) v_4258 v_4259) (concat (mux (ugt v_4262 v_4263) v_4262 v_4263) (mux (ugt v_4266 v_4267) v_4266 v_4267))));
      pure ()
    pat_end;
    pattern fun (v_2510 : reg (bv 256)) (v_2511 : reg (bv 256)) (v_2512 : reg (bv 256)) => do
      v_4279 <- getRegister v_2511;
      v_4280 <- eval (extract v_4279 0 32);
      v_4281 <- getRegister v_2510;
      v_4282 <- eval (extract v_4281 0 32);
      v_4285 <- eval (extract v_4279 32 64);
      v_4286 <- eval (extract v_4281 32 64);
      v_4289 <- eval (extract v_4279 64 96);
      v_4290 <- eval (extract v_4281 64 96);
      v_4293 <- eval (extract v_4279 96 128);
      v_4294 <- eval (extract v_4281 96 128);
      v_4297 <- eval (extract v_4279 128 160);
      v_4298 <- eval (extract v_4281 128 160);
      v_4301 <- eval (extract v_4279 160 192);
      v_4302 <- eval (extract v_4281 160 192);
      v_4305 <- eval (extract v_4279 192 224);
      v_4306 <- eval (extract v_4281 192 224);
      v_4309 <- eval (extract v_4279 224 256);
      v_4310 <- eval (extract v_4281 224 256);
      setRegister (lhs.of_reg v_2512) (concat (mux (ugt v_4280 v_4282) v_4280 v_4282) (concat (mux (ugt v_4285 v_4286) v_4285 v_4286) (concat (mux (ugt v_4289 v_4290) v_4289 v_4290) (concat (mux (ugt v_4293 v_4294) v_4293 v_4294) (concat (mux (ugt v_4297 v_4298) v_4297 v_4298) (concat (mux (ugt v_4301 v_4302) v_4301 v_4302) (concat (mux (ugt v_4305 v_4306) v_4305 v_4306) (mux (ugt v_4309 v_4310) v_4309 v_4310))))))));
      pure ()
    pat_end;
    pattern fun (v_2493 : Mem) (v_2494 : reg (bv 128)) (v_2495 : reg (bv 128)) => do
      v_10941 <- getRegister v_2494;
      v_10942 <- eval (extract v_10941 0 32);
      v_10943 <- evaluateAddress v_2493;
      v_10944 <- load v_10943 16;
      v_10945 <- eval (extract v_10944 0 32);
      v_10948 <- eval (extract v_10941 32 64);
      v_10949 <- eval (extract v_10944 32 64);
      v_10952 <- eval (extract v_10941 64 96);
      v_10953 <- eval (extract v_10944 64 96);
      v_10956 <- eval (extract v_10941 96 128);
      v_10957 <- eval (extract v_10944 96 128);
      setRegister (lhs.of_reg v_2495) (concat (mux (ugt v_10942 v_10945) v_10942 v_10945) (concat (mux (ugt v_10948 v_10949) v_10948 v_10949) (concat (mux (ugt v_10952 v_10953) v_10952 v_10953) (mux (ugt v_10956 v_10957) v_10956 v_10957))));
      pure ()
    pat_end;
    pattern fun (v_2504 : Mem) (v_2505 : reg (bv 256)) (v_2506 : reg (bv 256)) => do
      v_10964 <- getRegister v_2505;
      v_10965 <- eval (extract v_10964 0 32);
      v_10966 <- evaluateAddress v_2504;
      v_10967 <- load v_10966 32;
      v_10968 <- eval (extract v_10967 0 32);
      v_10971 <- eval (extract v_10964 32 64);
      v_10972 <- eval (extract v_10967 32 64);
      v_10975 <- eval (extract v_10964 64 96);
      v_10976 <- eval (extract v_10967 64 96);
      v_10979 <- eval (extract v_10964 96 128);
      v_10980 <- eval (extract v_10967 96 128);
      v_10983 <- eval (extract v_10964 128 160);
      v_10984 <- eval (extract v_10967 128 160);
      v_10987 <- eval (extract v_10964 160 192);
      v_10988 <- eval (extract v_10967 160 192);
      v_10991 <- eval (extract v_10964 192 224);
      v_10992 <- eval (extract v_10967 192 224);
      v_10995 <- eval (extract v_10964 224 256);
      v_10996 <- eval (extract v_10967 224 256);
      setRegister (lhs.of_reg v_2506) (concat (mux (ugt v_10965 v_10968) v_10965 v_10968) (concat (mux (ugt v_10971 v_10972) v_10971 v_10972) (concat (mux (ugt v_10975 v_10976) v_10975 v_10976) (concat (mux (ugt v_10979 v_10980) v_10979 v_10980) (concat (mux (ugt v_10983 v_10984) v_10983 v_10984) (concat (mux (ugt v_10987 v_10988) v_10987 v_10988) (concat (mux (ugt v_10991 v_10992) v_10991 v_10992) (mux (ugt v_10995 v_10996) v_10995 v_10996))))))));
      pure ()
    pat_end
