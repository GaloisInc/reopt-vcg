def vpsubsw1 : instruction :=
  definst "vpsubsw" $ do
    pattern fun (v_2565 : reg (bv 128)) (v_2566 : reg (bv 128)) (v_2567 : reg (bv 128)) => do
      v_4854 <- getRegister v_2566;
      v_4857 <- getRegister v_2565;
      v_4860 <- eval (sub (sext (extract v_4854 0 16) 18) (sext (extract v_4857 0 16) 18));
      v_4870 <- eval (sub (sext (extract v_4854 16 32) 18) (sext (extract v_4857 16 32) 18));
      v_4880 <- eval (sub (sext (extract v_4854 32 48) 18) (sext (extract v_4857 32 48) 18));
      v_4890 <- eval (sub (sext (extract v_4854 48 64) 18) (sext (extract v_4857 48 64) 18));
      v_4900 <- eval (sub (sext (extract v_4854 64 80) 18) (sext (extract v_4857 64 80) 18));
      v_4910 <- eval (sub (sext (extract v_4854 80 96) 18) (sext (extract v_4857 80 96) 18));
      v_4920 <- eval (sub (sext (extract v_4854 96 112) 18) (sext (extract v_4857 96 112) 18));
      v_4930 <- eval (sub (sext (extract v_4854 112 128) 18) (sext (extract v_4857 112 128) 18));
      setRegister (lhs.of_reg v_2567) (concat (mux (sgt v_4860 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_4860 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_4860 2 18))) (concat (mux (sgt v_4870 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_4870 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_4870 2 18))) (concat (mux (sgt v_4880 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_4880 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_4880 2 18))) (concat (mux (sgt v_4890 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_4890 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_4890 2 18))) (concat (mux (sgt v_4900 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_4900 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_4900 2 18))) (concat (mux (sgt v_4910 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_4910 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_4910 2 18))) (concat (mux (sgt v_4920 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_4920 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_4920 2 18))) (mux (sgt v_4930 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_4930 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_4930 2 18))))))))));
      pure ()
    pat_end;
    pattern fun (v_2576 : reg (bv 256)) (v_2577 : reg (bv 256)) (v_2578 : reg (bv 256)) => do
      v_4949 <- getRegister v_2577;
      v_4952 <- getRegister v_2576;
      v_4955 <- eval (sub (sext (extract v_4949 0 16) 18) (sext (extract v_4952 0 16) 18));
      v_4965 <- eval (sub (sext (extract v_4949 16 32) 18) (sext (extract v_4952 16 32) 18));
      v_4975 <- eval (sub (sext (extract v_4949 32 48) 18) (sext (extract v_4952 32 48) 18));
      v_4985 <- eval (sub (sext (extract v_4949 48 64) 18) (sext (extract v_4952 48 64) 18));
      v_4995 <- eval (sub (sext (extract v_4949 64 80) 18) (sext (extract v_4952 64 80) 18));
      v_5005 <- eval (sub (sext (extract v_4949 80 96) 18) (sext (extract v_4952 80 96) 18));
      v_5015 <- eval (sub (sext (extract v_4949 96 112) 18) (sext (extract v_4952 96 112) 18));
      v_5025 <- eval (sub (sext (extract v_4949 112 128) 18) (sext (extract v_4952 112 128) 18));
      v_5035 <- eval (sub (sext (extract v_4949 128 144) 18) (sext (extract v_4952 128 144) 18));
      v_5045 <- eval (sub (sext (extract v_4949 144 160) 18) (sext (extract v_4952 144 160) 18));
      v_5055 <- eval (sub (sext (extract v_4949 160 176) 18) (sext (extract v_4952 160 176) 18));
      v_5065 <- eval (sub (sext (extract v_4949 176 192) 18) (sext (extract v_4952 176 192) 18));
      v_5075 <- eval (sub (sext (extract v_4949 192 208) 18) (sext (extract v_4952 192 208) 18));
      v_5085 <- eval (sub (sext (extract v_4949 208 224) 18) (sext (extract v_4952 208 224) 18));
      v_5095 <- eval (sub (sext (extract v_4949 224 240) 18) (sext (extract v_4952 224 240) 18));
      v_5105 <- eval (sub (sext (extract v_4949 240 256) 18) (sext (extract v_4952 240 256) 18));
      setRegister (lhs.of_reg v_2578) (concat (mux (sgt v_4955 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_4955 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_4955 2 18))) (concat (mux (sgt v_4965 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_4965 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_4965 2 18))) (concat (mux (sgt v_4975 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_4975 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_4975 2 18))) (concat (mux (sgt v_4985 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_4985 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_4985 2 18))) (concat (mux (sgt v_4995 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_4995 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_4995 2 18))) (concat (mux (sgt v_5005 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_5005 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_5005 2 18))) (concat (mux (sgt v_5015 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_5015 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_5015 2 18))) (concat (mux (sgt v_5025 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_5025 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_5025 2 18))) (concat (mux (sgt v_5035 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_5035 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_5035 2 18))) (concat (mux (sgt v_5045 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_5045 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_5045 2 18))) (concat (mux (sgt v_5055 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_5055 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_5055 2 18))) (concat (mux (sgt v_5065 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_5065 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_5065 2 18))) (concat (mux (sgt v_5075 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_5075 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_5075 2 18))) (concat (mux (sgt v_5085 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_5085 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_5085 2 18))) (concat (mux (sgt v_5095 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_5095 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_5095 2 18))) (mux (sgt v_5105 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_5105 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_5105 2 18))))))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_2559 : Mem) (v_2560 : reg (bv 128)) (v_2561 : reg (bv 128)) => do
      v_10982 <- getRegister v_2560;
      v_10985 <- evaluateAddress v_2559;
      v_10986 <- load v_10985 16;
      v_10989 <- eval (sub (sext (extract v_10982 0 16) 18) (sext (extract v_10986 0 16) 18));
      v_10999 <- eval (sub (sext (extract v_10982 16 32) 18) (sext (extract v_10986 16 32) 18));
      v_11009 <- eval (sub (sext (extract v_10982 32 48) 18) (sext (extract v_10986 32 48) 18));
      v_11019 <- eval (sub (sext (extract v_10982 48 64) 18) (sext (extract v_10986 48 64) 18));
      v_11029 <- eval (sub (sext (extract v_10982 64 80) 18) (sext (extract v_10986 64 80) 18));
      v_11039 <- eval (sub (sext (extract v_10982 80 96) 18) (sext (extract v_10986 80 96) 18));
      v_11049 <- eval (sub (sext (extract v_10982 96 112) 18) (sext (extract v_10986 96 112) 18));
      v_11059 <- eval (sub (sext (extract v_10982 112 128) 18) (sext (extract v_10986 112 128) 18));
      setRegister (lhs.of_reg v_2561) (concat (mux (sgt v_10989 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_10989 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_10989 2 18))) (concat (mux (sgt v_10999 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_10999 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_10999 2 18))) (concat (mux (sgt v_11009 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_11009 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_11009 2 18))) (concat (mux (sgt v_11019 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_11019 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_11019 2 18))) (concat (mux (sgt v_11029 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_11029 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_11029 2 18))) (concat (mux (sgt v_11039 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_11039 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_11039 2 18))) (concat (mux (sgt v_11049 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_11049 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_11049 2 18))) (mux (sgt v_11059 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_11059 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_11059 2 18))))))))));
      pure ()
    pat_end;
    pattern fun (v_2570 : Mem) (v_2571 : reg (bv 256)) (v_2572 : reg (bv 256)) => do
      v_11073 <- getRegister v_2571;
      v_11076 <- evaluateAddress v_2570;
      v_11077 <- load v_11076 32;
      v_11080 <- eval (sub (sext (extract v_11073 0 16) 18) (sext (extract v_11077 0 16) 18));
      v_11090 <- eval (sub (sext (extract v_11073 16 32) 18) (sext (extract v_11077 16 32) 18));
      v_11100 <- eval (sub (sext (extract v_11073 32 48) 18) (sext (extract v_11077 32 48) 18));
      v_11110 <- eval (sub (sext (extract v_11073 48 64) 18) (sext (extract v_11077 48 64) 18));
      v_11120 <- eval (sub (sext (extract v_11073 64 80) 18) (sext (extract v_11077 64 80) 18));
      v_11130 <- eval (sub (sext (extract v_11073 80 96) 18) (sext (extract v_11077 80 96) 18));
      v_11140 <- eval (sub (sext (extract v_11073 96 112) 18) (sext (extract v_11077 96 112) 18));
      v_11150 <- eval (sub (sext (extract v_11073 112 128) 18) (sext (extract v_11077 112 128) 18));
      v_11160 <- eval (sub (sext (extract v_11073 128 144) 18) (sext (extract v_11077 128 144) 18));
      v_11170 <- eval (sub (sext (extract v_11073 144 160) 18) (sext (extract v_11077 144 160) 18));
      v_11180 <- eval (sub (sext (extract v_11073 160 176) 18) (sext (extract v_11077 160 176) 18));
      v_11190 <- eval (sub (sext (extract v_11073 176 192) 18) (sext (extract v_11077 176 192) 18));
      v_11200 <- eval (sub (sext (extract v_11073 192 208) 18) (sext (extract v_11077 192 208) 18));
      v_11210 <- eval (sub (sext (extract v_11073 208 224) 18) (sext (extract v_11077 208 224) 18));
      v_11220 <- eval (sub (sext (extract v_11073 224 240) 18) (sext (extract v_11077 224 240) 18));
      v_11230 <- eval (sub (sext (extract v_11073 240 256) 18) (sext (extract v_11077 240 256) 18));
      setRegister (lhs.of_reg v_2572) (concat (mux (sgt v_11080 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_11080 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_11080 2 18))) (concat (mux (sgt v_11090 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_11090 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_11090 2 18))) (concat (mux (sgt v_11100 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_11100 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_11100 2 18))) (concat (mux (sgt v_11110 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_11110 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_11110 2 18))) (concat (mux (sgt v_11120 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_11120 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_11120 2 18))) (concat (mux (sgt v_11130 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_11130 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_11130 2 18))) (concat (mux (sgt v_11140 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_11140 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_11140 2 18))) (concat (mux (sgt v_11150 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_11150 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_11150 2 18))) (concat (mux (sgt v_11160 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_11160 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_11160 2 18))) (concat (mux (sgt v_11170 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_11170 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_11170 2 18))) (concat (mux (sgt v_11180 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_11180 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_11180 2 18))) (concat (mux (sgt v_11190 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_11190 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_11190 2 18))) (concat (mux (sgt v_11200 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_11200 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_11200 2 18))) (concat (mux (sgt v_11210 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_11210 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_11210 2 18))) (concat (mux (sgt v_11220 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_11220 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_11220 2 18))) (mux (sgt v_11230 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_11230 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_11230 2 18))))))))))))))))));
      pure ()
    pat_end
