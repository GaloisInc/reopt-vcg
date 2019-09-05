def pminsw1 : instruction :=
  definst "pminsw" $ do
    pattern fun (v_2683 : reg (bv 128)) (v_2684 : reg (bv 128)) => do
      v_5160 <- getRegister v_2684;
      v_5161 <- eval (extract v_5160 0 16);
      v_5162 <- getRegister v_2683;
      v_5163 <- eval (extract v_5162 0 16);
      v_5166 <- eval (extract v_5160 16 32);
      v_5167 <- eval (extract v_5162 16 32);
      v_5170 <- eval (extract v_5160 32 48);
      v_5171 <- eval (extract v_5162 32 48);
      v_5174 <- eval (extract v_5160 48 64);
      v_5175 <- eval (extract v_5162 48 64);
      v_5178 <- eval (extract v_5160 64 80);
      v_5179 <- eval (extract v_5162 64 80);
      v_5182 <- eval (extract v_5160 80 96);
      v_5183 <- eval (extract v_5162 80 96);
      v_5186 <- eval (extract v_5160 96 112);
      v_5187 <- eval (extract v_5162 96 112);
      v_5190 <- eval (extract v_5160 112 128);
      v_5191 <- eval (extract v_5162 112 128);
      setRegister (lhs.of_reg v_2684) (concat (mux (slt v_5161 v_5163) v_5161 v_5163) (concat (mux (slt v_5166 v_5167) v_5166 v_5167) (concat (mux (slt v_5170 v_5171) v_5170 v_5171) (concat (mux (slt v_5174 v_5175) v_5174 v_5175) (concat (mux (slt v_5178 v_5179) v_5178 v_5179) (concat (mux (slt v_5182 v_5183) v_5182 v_5183) (concat (mux (slt v_5186 v_5187) v_5186 v_5187) (mux (slt v_5190 v_5191) v_5190 v_5191))))))));
      pure ()
    pat_end;
    pattern fun (v_2680 : Mem) (v_2679 : reg (bv 128)) => do
      v_12040 <- getRegister v_2679;
      v_12041 <- eval (extract v_12040 0 16);
      v_12042 <- evaluateAddress v_2680;
      v_12043 <- load v_12042 16;
      v_12044 <- eval (extract v_12043 0 16);
      v_12047 <- eval (extract v_12040 16 32);
      v_12048 <- eval (extract v_12043 16 32);
      v_12051 <- eval (extract v_12040 32 48);
      v_12052 <- eval (extract v_12043 32 48);
      v_12055 <- eval (extract v_12040 48 64);
      v_12056 <- eval (extract v_12043 48 64);
      v_12059 <- eval (extract v_12040 64 80);
      v_12060 <- eval (extract v_12043 64 80);
      v_12063 <- eval (extract v_12040 80 96);
      v_12064 <- eval (extract v_12043 80 96);
      v_12067 <- eval (extract v_12040 96 112);
      v_12068 <- eval (extract v_12043 96 112);
      v_12071 <- eval (extract v_12040 112 128);
      v_12072 <- eval (extract v_12043 112 128);
      setRegister (lhs.of_reg v_2679) (concat (mux (slt v_12041 v_12044) v_12041 v_12044) (concat (mux (slt v_12047 v_12048) v_12047 v_12048) (concat (mux (slt v_12051 v_12052) v_12051 v_12052) (concat (mux (slt v_12055 v_12056) v_12055 v_12056) (concat (mux (slt v_12059 v_12060) v_12059 v_12060) (concat (mux (slt v_12063 v_12064) v_12063 v_12064) (concat (mux (slt v_12067 v_12068) v_12067 v_12068) (mux (slt v_12071 v_12072) v_12071 v_12072))))))));
      pure ()
    pat_end
