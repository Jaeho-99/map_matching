function plot_record(id)
  % load the record
  fn = sprintf('./%08d/%08d', id, id);
  track = dlmread([fn,'.track'], '\t');
  route = dlmread([fn,'.route'], '\t');
  nodes = dlmread([fn,'.nodes'], '\t');
  arcs = dlmread([fn,'.arcs'], '\t');
  
  figure;
  hold on;
  xmargin = (-min(nodes(:,1))+max(nodes(:,1)))/20;
  ymargin = (-min(nodes(:,2))+max(nodes(:,2)))/20;
  axis([min(nodes(:,1))-xmargin, max(nodes(:,1))+xmargin, ...
        min(nodes(:,2))-ymargin, max(nodes(:,2))+ymargin]);

  % render the map
  for i=1:size(arcs,1)
    arc(1,:) = nodes(arcs(i,1)+1, 1:2);
    arc(2,:) = nodes(arcs(i,2)+1, 1:2);
    plot(arc(:,1), arc(:,2));
  end
  
  % render the track
  plot(track(:,1), track(:,2), '.');
  
  % render the route
  for i=1:size(route,1)
    arc(1,:) = nodes(arcs(route(i)+1,1)+1, 1:2);
    arc(2,:) = nodes(arcs(route(i)+1,2)+1, 1:2);
    plot(arc(:,1), arc(:,2), 'k', 'LineWidth', 2);
  end
end
