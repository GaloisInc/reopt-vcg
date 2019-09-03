def pmaxub1 : instruction :=
  definst "pmaxub" $ do
    pattern fun (v_2575 : reg (bv 128)) (v_2576 : reg (bv 128)) => do
      v_4926 <- getRegister v_2576;
      v_4927 <- eval (extract v_4926 0 8);
      v_4928 <- getRegister v_2575;
      v_4929 <- eval (extract v_4928 0 8);
      v_4932 <- eval (extract v_4926 8 16);
      v_4933 <- eval (extract v_4928 8 16);
      v_4936 <- eval (extract v_4926 16 24);
      v_4937 <- eval (extract v_4928 16 24);
      v_4940 <- eval (extract v_4926 24 32);
      v_4941 <- eval (extract v_4928 24 32);
      v_4944 <- eval (extract v_4926 32 40);
      v_4945 <- eval (extract v_4928 32 40);
      v_4948 <- eval (extract v_4926 40 48);
      v_4949 <- eval (extract v_4928 40 48);
      v_4952 <- eval (extract v_4926 48 56);
      v_4953 <- eval (extract v_4928 48 56);
      v_4956 <- eval (extract v_4926 56 64);
      v_4957 <- eval (extract v_4928 56 64);
      v_4960 <- eval (extract v_4926 64 72);
      v_4961 <- eval (extract v_4928 64 72);
      v_4964 <- eval (extract v_4926 72 80);
      v_4965 <- eval (extract v_4928 72 80);
      v_4968 <- eval (extract v_4926 80 88);
      v_4969 <- eval (extract v_4928 80 88);
      v_4972 <- eval (extract v_4926 88 96);
      v_4973 <- eval (extract v_4928 88 96);
      v_4976 <- eval (extract v_4926 96 104);
      v_4977 <- eval (extract v_4928 96 104);
      v_4980 <- eval (extract v_4926 104 112);
      v_4981 <- eval (extract v_4928 104 112);
      v_4984 <- eval (extract v_4926 112 120);
      v_4985 <- eval (extract v_4928 112 120);
      v_4988 <- eval (extract v_4926 120 128);
      v_4989 <- eval (extract v_4928 120 128);
      setRegister (lhs.of_reg v_2576) (concat (mux (ugt v_4927 v_4929) v_4927 v_4929) (concat (mux (ugt v_4932 v_4933) v_4932 v_4933) (concat (mux (ugt v_4936 v_4937) v_4936 v_4937) (concat (mux (ugt v_4940 v_4941) v_4940 v_4941) (concat (mux (ugt v_4944 v_4945) v_4944 v_4945) (concat (mux (ugt v_4948 v_4949) v_4948 v_4949) (concat (mux (ugt v_4952 v_4953) v_4952 v_4953) (concat (mux (ugt v_4956 v_4957) v_4956 v_4957) (concat (mux (ugt v_4960 v_4961) v_4960 v_4961) (concat (mux (ugt v_4964 v_4965) v_4964 v_4965) (concat (mux (ugt v_4968 v_4969) v_4968 v_4969) (concat (mux (ugt v_4972 v_4973) v_4972 v_4973) (concat (mux (ugt v_4976 v_4977) v_4976 v_4977) (concat (mux (ugt v_4980 v_4981) v_4980 v_4981) (concat (mux (ugt v_4984 v_4985) v_4984 v_4985) (mux (ugt v_4988 v_4989) v_4988 v_4989))))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_2570 : Mem) (v_2571 : reg (bv 128)) => do
      v_12320 <- getRegister v_2571;
      v_12321 <- eval (extract v_12320 0 8);
      v_12322 <- evaluateAddress v_2570;
      v_12323 <- load v_12322 16;
      v_12324 <- eval (extract v_12323 0 8);
      v_12327 <- eval (extract v_12320 8 16);
      v_12328 <- eval (extract v_12323 8 16);
      v_12331 <- eval (extract v_12320 16 24);
      v_12332 <- eval (extract v_12323 16 24);
      v_12335 <- eval (extract v_12320 24 32);
      v_12336 <- eval (extract v_12323 24 32);
      v_12339 <- eval (extract v_12320 32 40);
      v_12340 <- eval (extract v_12323 32 40);
      v_12343 <- eval (extract v_12320 40 48);
      v_12344 <- eval (extract v_12323 40 48);
      v_12347 <- eval (extract v_12320 48 56);
      v_12348 <- eval (extract v_12323 48 56);
      v_12351 <- eval (extract v_12320 56 64);
      v_12352 <- eval (extract v_12323 56 64);
      v_12355 <- eval (extract v_12320 64 72);
      v_12356 <- eval (extract v_12323 64 72);
      v_12359 <- eval (extract v_12320 72 80);
      v_12360 <- eval (extract v_12323 72 80);
      v_12363 <- eval (extract v_12320 80 88);
      v_12364 <- eval (extract v_12323 80 88);
      v_12367 <- eval (extract v_12320 88 96);
      v_12368 <- eval (extract v_12323 88 96);
      v_12371 <- eval (extract v_12320 96 104);
      v_12372 <- eval (extract v_12323 96 104);
      v_12375 <- eval (extract v_12320 104 112);
      v_12376 <- eval (extract v_12323 104 112);
      v_12379 <- eval (extract v_12320 112 120);
      v_12380 <- eval (extract v_12323 112 120);
      v_12383 <- eval (extract v_12320 120 128);
      v_12384 <- eval (extract v_12323 120 128);
      setRegister (lhs.of_reg v_2571) (concat (mux (ugt v_12321 v_12324) v_12321 v_12324) (concat (mux (ugt v_12327 v_12328) v_12327 v_12328) (concat (mux (ugt v_12331 v_12332) v_12331 v_12332) (concat (mux (ugt v_12335 v_12336) v_12335 v_12336) (concat (mux (ugt v_12339 v_12340) v_12339 v_12340) (concat (mux (ugt v_12343 v_12344) v_12343 v_12344) (concat (mux (ugt v_12347 v_12348) v_12347 v_12348) (concat (mux (ugt v_12351 v_12352) v_12351 v_12352) (concat (mux (ugt v_12355 v_12356) v_12355 v_12356) (concat (mux (ugt v_12359 v_12360) v_12359 v_12360) (concat (mux (ugt v_12363 v_12364) v_12363 v_12364) (concat (mux (ugt v_12367 v_12368) v_12367 v_12368) (concat (mux (ugt v_12371 v_12372) v_12371 v_12372) (concat (mux (ugt v_12375 v_12376) v_12375 v_12376) (concat (mux (ugt v_12379 v_12380) v_12379 v_12380) (mux (ugt v_12383 v_12384) v_12383 v_12384))))))))))))))));
      pure ()
    pat_end
