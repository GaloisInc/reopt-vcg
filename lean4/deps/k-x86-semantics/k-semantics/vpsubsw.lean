def vpsubsw1 : instruction :=
  definst "vpsubsw" $ do
    pattern fun (v_2538 : reg (bv 128)) (v_2539 : reg (bv 128)) (v_2540 : reg (bv 128)) => do
      v_4827 <- getRegister v_2539;
      v_4830 <- getRegister v_2538;
      v_4833 <- eval (sub (sext (extract v_4827 0 16) 18) (sext (extract v_4830 0 16) 18));
      v_4843 <- eval (sub (sext (extract v_4827 16 32) 18) (sext (extract v_4830 16 32) 18));
      v_4853 <- eval (sub (sext (extract v_4827 32 48) 18) (sext (extract v_4830 32 48) 18));
      v_4863 <- eval (sub (sext (extract v_4827 48 64) 18) (sext (extract v_4830 48 64) 18));
      v_4873 <- eval (sub (sext (extract v_4827 64 80) 18) (sext (extract v_4830 64 80) 18));
      v_4883 <- eval (sub (sext (extract v_4827 80 96) 18) (sext (extract v_4830 80 96) 18));
      v_4893 <- eval (sub (sext (extract v_4827 96 112) 18) (sext (extract v_4830 96 112) 18));
      v_4903 <- eval (sub (sext (extract v_4827 112 128) 18) (sext (extract v_4830 112 128) 18));
      setRegister (lhs.of_reg v_2540) (concat (mux (sgt v_4833 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_4833 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_4833 2 18))) (concat (mux (sgt v_4843 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_4843 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_4843 2 18))) (concat (mux (sgt v_4853 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_4853 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_4853 2 18))) (concat (mux (sgt v_4863 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_4863 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_4863 2 18))) (concat (mux (sgt v_4873 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_4873 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_4873 2 18))) (concat (mux (sgt v_4883 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_4883 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_4883 2 18))) (concat (mux (sgt v_4893 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_4893 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_4893 2 18))) (mux (sgt v_4903 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_4903 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_4903 2 18))))))))));
      pure ()
    pat_end;
    pattern fun (v_2549 : reg (bv 256)) (v_2550 : reg (bv 256)) (v_2551 : reg (bv 256)) => do
      v_4922 <- getRegister v_2550;
      v_4925 <- getRegister v_2549;
      v_4928 <- eval (sub (sext (extract v_4922 0 16) 18) (sext (extract v_4925 0 16) 18));
      v_4938 <- eval (sub (sext (extract v_4922 16 32) 18) (sext (extract v_4925 16 32) 18));
      v_4948 <- eval (sub (sext (extract v_4922 32 48) 18) (sext (extract v_4925 32 48) 18));
      v_4958 <- eval (sub (sext (extract v_4922 48 64) 18) (sext (extract v_4925 48 64) 18));
      v_4968 <- eval (sub (sext (extract v_4922 64 80) 18) (sext (extract v_4925 64 80) 18));
      v_4978 <- eval (sub (sext (extract v_4922 80 96) 18) (sext (extract v_4925 80 96) 18));
      v_4988 <- eval (sub (sext (extract v_4922 96 112) 18) (sext (extract v_4925 96 112) 18));
      v_4998 <- eval (sub (sext (extract v_4922 112 128) 18) (sext (extract v_4925 112 128) 18));
      v_5008 <- eval (sub (sext (extract v_4922 128 144) 18) (sext (extract v_4925 128 144) 18));
      v_5018 <- eval (sub (sext (extract v_4922 144 160) 18) (sext (extract v_4925 144 160) 18));
      v_5028 <- eval (sub (sext (extract v_4922 160 176) 18) (sext (extract v_4925 160 176) 18));
      v_5038 <- eval (sub (sext (extract v_4922 176 192) 18) (sext (extract v_4925 176 192) 18));
      v_5048 <- eval (sub (sext (extract v_4922 192 208) 18) (sext (extract v_4925 192 208) 18));
      v_5058 <- eval (sub (sext (extract v_4922 208 224) 18) (sext (extract v_4925 208 224) 18));
      v_5068 <- eval (sub (sext (extract v_4922 224 240) 18) (sext (extract v_4925 224 240) 18));
      v_5078 <- eval (sub (sext (extract v_4922 240 256) 18) (sext (extract v_4925 240 256) 18));
      setRegister (lhs.of_reg v_2551) (concat (mux (sgt v_4928 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_4928 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_4928 2 18))) (concat (mux (sgt v_4938 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_4938 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_4938 2 18))) (concat (mux (sgt v_4948 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_4948 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_4948 2 18))) (concat (mux (sgt v_4958 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_4958 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_4958 2 18))) (concat (mux (sgt v_4968 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_4968 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_4968 2 18))) (concat (mux (sgt v_4978 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_4978 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_4978 2 18))) (concat (mux (sgt v_4988 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_4988 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_4988 2 18))) (concat (mux (sgt v_4998 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_4998 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_4998 2 18))) (concat (mux (sgt v_5008 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_5008 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_5008 2 18))) (concat (mux (sgt v_5018 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_5018 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_5018 2 18))) (concat (mux (sgt v_5028 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_5028 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_5028 2 18))) (concat (mux (sgt v_5038 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_5038 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_5038 2 18))) (concat (mux (sgt v_5048 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_5048 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_5048 2 18))) (concat (mux (sgt v_5058 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_5058 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_5058 2 18))) (concat (mux (sgt v_5068 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_5068 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_5068 2 18))) (mux (sgt v_5078 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_5078 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_5078 2 18))))))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_2532 : Mem) (v_2533 : reg (bv 128)) (v_2534 : reg (bv 128)) => do
      v_10955 <- getRegister v_2533;
      v_10958 <- evaluateAddress v_2532;
      v_10959 <- load v_10958 16;
      v_10962 <- eval (sub (sext (extract v_10955 0 16) 18) (sext (extract v_10959 0 16) 18));
      v_10972 <- eval (sub (sext (extract v_10955 16 32) 18) (sext (extract v_10959 16 32) 18));
      v_10982 <- eval (sub (sext (extract v_10955 32 48) 18) (sext (extract v_10959 32 48) 18));
      v_10992 <- eval (sub (sext (extract v_10955 48 64) 18) (sext (extract v_10959 48 64) 18));
      v_11002 <- eval (sub (sext (extract v_10955 64 80) 18) (sext (extract v_10959 64 80) 18));
      v_11012 <- eval (sub (sext (extract v_10955 80 96) 18) (sext (extract v_10959 80 96) 18));
      v_11022 <- eval (sub (sext (extract v_10955 96 112) 18) (sext (extract v_10959 96 112) 18));
      v_11032 <- eval (sub (sext (extract v_10955 112 128) 18) (sext (extract v_10959 112 128) 18));
      setRegister (lhs.of_reg v_2534) (concat (mux (sgt v_10962 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_10962 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_10962 2 18))) (concat (mux (sgt v_10972 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_10972 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_10972 2 18))) (concat (mux (sgt v_10982 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_10982 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_10982 2 18))) (concat (mux (sgt v_10992 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_10992 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_10992 2 18))) (concat (mux (sgt v_11002 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_11002 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_11002 2 18))) (concat (mux (sgt v_11012 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_11012 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_11012 2 18))) (concat (mux (sgt v_11022 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_11022 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_11022 2 18))) (mux (sgt v_11032 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_11032 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_11032 2 18))))))))));
      pure ()
    pat_end;
    pattern fun (v_2543 : Mem) (v_2544 : reg (bv 256)) (v_2545 : reg (bv 256)) => do
      v_11046 <- getRegister v_2544;
      v_11049 <- evaluateAddress v_2543;
      v_11050 <- load v_11049 32;
      v_11053 <- eval (sub (sext (extract v_11046 0 16) 18) (sext (extract v_11050 0 16) 18));
      v_11063 <- eval (sub (sext (extract v_11046 16 32) 18) (sext (extract v_11050 16 32) 18));
      v_11073 <- eval (sub (sext (extract v_11046 32 48) 18) (sext (extract v_11050 32 48) 18));
      v_11083 <- eval (sub (sext (extract v_11046 48 64) 18) (sext (extract v_11050 48 64) 18));
      v_11093 <- eval (sub (sext (extract v_11046 64 80) 18) (sext (extract v_11050 64 80) 18));
      v_11103 <- eval (sub (sext (extract v_11046 80 96) 18) (sext (extract v_11050 80 96) 18));
      v_11113 <- eval (sub (sext (extract v_11046 96 112) 18) (sext (extract v_11050 96 112) 18));
      v_11123 <- eval (sub (sext (extract v_11046 112 128) 18) (sext (extract v_11050 112 128) 18));
      v_11133 <- eval (sub (sext (extract v_11046 128 144) 18) (sext (extract v_11050 128 144) 18));
      v_11143 <- eval (sub (sext (extract v_11046 144 160) 18) (sext (extract v_11050 144 160) 18));
      v_11153 <- eval (sub (sext (extract v_11046 160 176) 18) (sext (extract v_11050 160 176) 18));
      v_11163 <- eval (sub (sext (extract v_11046 176 192) 18) (sext (extract v_11050 176 192) 18));
      v_11173 <- eval (sub (sext (extract v_11046 192 208) 18) (sext (extract v_11050 192 208) 18));
      v_11183 <- eval (sub (sext (extract v_11046 208 224) 18) (sext (extract v_11050 208 224) 18));
      v_11193 <- eval (sub (sext (extract v_11046 224 240) 18) (sext (extract v_11050 224 240) 18));
      v_11203 <- eval (sub (sext (extract v_11046 240 256) 18) (sext (extract v_11050 240 256) 18));
      setRegister (lhs.of_reg v_2545) (concat (mux (sgt v_11053 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_11053 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_11053 2 18))) (concat (mux (sgt v_11063 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_11063 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_11063 2 18))) (concat (mux (sgt v_11073 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_11073 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_11073 2 18))) (concat (mux (sgt v_11083 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_11083 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_11083 2 18))) (concat (mux (sgt v_11093 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_11093 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_11093 2 18))) (concat (mux (sgt v_11103 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_11103 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_11103 2 18))) (concat (mux (sgt v_11113 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_11113 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_11113 2 18))) (concat (mux (sgt v_11123 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_11123 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_11123 2 18))) (concat (mux (sgt v_11133 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_11133 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_11133 2 18))) (concat (mux (sgt v_11143 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_11143 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_11143 2 18))) (concat (mux (sgt v_11153 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_11153 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_11153 2 18))) (concat (mux (sgt v_11163 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_11163 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_11163 2 18))) (concat (mux (sgt v_11173 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_11173 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_11173 2 18))) (concat (mux (sgt v_11183 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_11183 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_11183 2 18))) (concat (mux (sgt v_11193 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_11193 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_11193 2 18))) (mux (sgt v_11203 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_11203 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_11203 2 18))))))))))))))))));
      pure ()
    pat_end
