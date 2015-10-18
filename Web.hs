 import Network
 import System.IO
 
 
 
 main = withSocketsDo $ do
 	h <- connectTo "http:www.google.com" (PortNumber 80)
 	hSetBuffering h LineBuffering
 	hPutStr h "GET / HTTP/1.1\nhost: www.google.com\n\n"
 	contents <- hGetContents h
 	putStrLn contents
 	hClose h
