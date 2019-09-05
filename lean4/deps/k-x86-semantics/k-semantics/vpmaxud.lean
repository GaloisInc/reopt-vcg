def vpmaxud1 : instruction :=
  definst "vpmaxud" $ do
    pattern fun (v_2472 : reg (bv 128)) (v_2473 : reg (bv 128)) (v_2474 : reg (bv 128)) => do
      v_4225 <- getRegister v_2473;
      v_4226 <- eval (extract v_4225 0 32);
      v_4227 <- getRegister v_2472;
      v_4228 <- eval (extract v_4227 0 32);
      v_4231 <- eval (extract v_4225 32 64);
      v_4232 <- eval (extract v_4227 32 64);
      v_4235 <- eval (extract v_4225 64 96);
      v_4236 <- eval (extract v_4227 64 96);
      v_4239 <- eval (extract v_4225 96 128);
      v_4240 <- eval (extract v_4227 96 128);
      setRegister (lhs.of_reg v_2474) (concat (mux (ugt v_4226 v_4228) v_4226 v_4228) (concat (mux (ugt v_4231 v_4232) v_4231 v_4232) (concat (mux (ugt v_4235 v_4236) v_4235 v_4236) (mux (ugt v_4239 v_4240) v_4239 v_4240))));
      pure ()
    pat_end;
    pattern fun (v_2483 : reg (bv 256)) (v_2484 : reg (bv 256)) (v_2485 : reg (bv 256)) => do
      v_4252 <- getRegister v_2484;
      v_4253 <- eval (extract v_4252 0 32);
      v_4254 <- getRegister v_2483;
      v_4255 <- eval (extract v_4254 0 32);
      v_4258 <- eval (extract v_4252 32 64);
      v_4259 <- eval (extract v_4254 32 64);
      v_4262 <- eval (extract v_4252 64 96);
      v_4263 <- eval (extract v_4254 64 96);
      v_4266 <- eval (extract v_4252 96 128);
      v_4267 <- eval (extract v_4254 96 128);
      v_4270 <- eval (extract v_4252 128 160);
      v_4271 <- eval (extract v_4254 128 160);
      v_4274 <- eval (extract v_4252 160 192);
      v_4275 <- eval (extract v_4254 160 192);
      v_4278 <- eval (extract v_4252 192 224);
      v_4279 <- eval (extract v_4254 192 224);
      v_4282 <- eval (extract v_4252 224 256);
      v_4283 <- eval (extract v_4254 224 256);
      setRegister (lhs.of_reg v_2485) (concat (mux (ugt v_4253 v_4255) v_4253 v_4255) (concat (mux (ugt v_4258 v_4259) v_4258 v_4259) (concat (mux (ugt v_4262 v_4263) v_4262 v_4263) (concat (mux (ugt v_4266 v_4267) v_4266 v_4267) (concat (mux (ugt v_4270 v_4271) v_4270 v_4271) (concat (mux (ugt v_4274 v_4275) v_4274 v_4275) (concat (mux (ugt v_4278 v_4279) v_4278 v_4279) (mux (ugt v_4282 v_4283) v_4282 v_4283))))))));
      pure ()
    pat_end;
    pattern fun (v_2466 : Mem) (v_2467 : reg (bv 128)) (v_2468 : reg (bv 128)) => do
      v_10914 <- getRegister v_2467;
      v_10915 <- eval (extract v_10914 0 32);
      v_10916 <- evaluateAddress v_2466;
      v_10917 <- load v_10916 16;
      v_10918 <- eval (extract v_10917 0 32);
      v_10921 <- eval (extract v_10914 32 64);
      v_10922 <- eval (extract v_10917 32 64);
      v_10925 <- eval (extract v_10914 64 96);
      v_10926 <- eval (extract v_10917 64 96);
      v_10929 <- eval (extract v_10914 96 128);
      v_10930 <- eval (extract v_10917 96 128);
      setRegister (lhs.of_reg v_2468) (concat (mux (ugt v_10915 v_10918) v_10915 v_10918) (concat (mux (ugt v_10921 v_10922) v_10921 v_10922) (concat (mux (ugt v_10925 v_10926) v_10925 v_10926) (mux (ugt v_10929 v_10930) v_10929 v_10930))));
      pure ()
    pat_end;
    pattern fun (v_2477 : Mem) (v_2478 : reg (bv 256)) (v_2479 : reg (bv 256)) => do
      v_10937 <- getRegister v_2478;
      v_10938 <- eval (extract v_10937 0 32);
      v_10939 <- evaluateAddress v_2477;
      v_10940 <- load v_10939 32;
      v_10941 <- eval (extract v_10940 0 32);
      v_10944 <- eval (extract v_10937 32 64);
      v_10945 <- eval (extract v_10940 32 64);
      v_10948 <- eval (extract v_10937 64 96);
      v_10949 <- eval (extract v_10940 64 96);
      v_10952 <- eval (extract v_10937 96 128);
      v_10953 <- eval (extract v_10940 96 128);
      v_10956 <- eval (extract v_10937 128 160);
      v_10957 <- eval (extract v_10940 128 160);
      v_10960 <- eval (extract v_10937 160 192);
      v_10961 <- eval (extract v_10940 160 192);
      v_10964 <- eval (extract v_10937 192 224);
      v_10965 <- eval (extract v_10940 192 224);
      v_10968 <- eval (extract v_10937 224 256);
      v_10969 <- eval (extract v_10940 224 256);
      setRegister (lhs.of_reg v_2479) (concat (mux (ugt v_10938 v_10941) v_10938 v_10941) (concat (mux (ugt v_10944 v_10945) v_10944 v_10945) (concat (mux (ugt v_10948 v_10949) v_10948 v_10949) (concat (mux (ugt v_10952 v_10953) v_10952 v_10953) (concat (mux (ugt v_10956 v_10957) v_10956 v_10957) (concat (mux (ugt v_10960 v_10961) v_10960 v_10961) (concat (mux (ugt v_10964 v_10965) v_10964 v_10965) (mux (ugt v_10968 v_10969) v_10968 v_10969))))))));
      pure ()
    pat_end
